-- Prove2me | solution 1 for Grunbaum2003.auto_GRU_M05_EFFECTIVE_TYPES_exists_computable_realizable_scheme_representatives
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T17:51:14.347967+00:00
-- url     : https://prove2.me/submissions/7758753c-13db-4c6e-944f-1fcf18c84cc7

import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_IsDPolytope
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_PolytopeFace
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_SchemeRealizes
import Theorems.Thm_Grunbaum2003_auto_GRU_M05_EFFECTIVE_TYPES_exists_schemeRealizes_iff_arithmetic_certificates
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem primrec_list_sublists {α : Type} [Primcodable α] :
    Primrec (@List.sublists' α) := by
  have hFold : Primrec (fun l : List α =>
      l.foldr (fun a r => r ++ r.map (List.cons a)) [[]]) := by
    apply Primrec.list_foldr
      (h := fun (_ : List α) (p : α × List (List α)) => p.2 ++ p.2.map (List.cons p.1))
      Primrec.id (Primrec.const [[]])
    change Primrec (fun p : List α × (α × List (List α)) =>
      p.2.2 ++ p.2.2.map (List.cons p.2.1))
    exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  apply hFold.of_eq
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.sublists'_cons, ih]

theorem primrec_list_product {α β : Type} [Primcodable α] [Primcodable β] :
    Primrec₂ (@List.product α β) := by
  have h : Primrec (fun p : List α × List β =>
      p.1.flatMap (fun a => p.2.map (fun b => (a, b)))) := by
    apply Primrec.list_flatMap Primrec.fst
    apply Primrec.list_map (Primrec.snd.comp Primrec.fst)
    exact ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  exact h

theorem primrec_list_mem {α : Type} [Primcodable α] [DecidableEq α] :
    PrimrecRel (fun (a : α) (L : List α) => a ∈ L) := by
  have h : PrimrecRel (fun (L : List α) (a : α) => ∃ b ∈ L, b = a) :=
    Primrec.eq.exists_mem_list
  exact (h.of_eq (fun L a => by simp)).swap

theorem primrec_bounded_list_forall {X A : Type} [Primcodable X] [Primcodable A]
    {L : X → List A} {P : X → A → Prop}
    (hL : Primrec L) (hP : PrimrecRel P) :
    PrimrecPred (fun x => ∀ a ∈ L x, P x a) :=
  hP.swap.forall_mem_list.comp hL Primrec.id

theorem primrec_bounded_list_exists {X A : Type} [Primcodable X] [Primcodable A]
    {L : X → List A} {P : X → A → Prop}
    (hL : Primrec L) (hP : PrimrecRel P) :
    PrimrecPred (fun x => ∃ a ∈ L x, P x a) :=
  hP.swap.exists_mem_list.comp hL Primrec.id

end Grunbaum2003

open scoped BigOperators

namespace Grunbaum2003.FormulaCompiler

inductive Term where
  | var : ℕ → Term
  | zero : Term
  | one : Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | neg : Term → Term
  deriving DecidableEq

inductive Formula where
  | truth : Bool → Formula
  | eq : Term → Term → Formula
  | lt : Term → Term → Formula
  | le : Term → Term → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | all : Formula → Formula
  | ex : Formula → Formula
  deriving DecidableEq

def consEnv (x : ℝ) (ρ : ℕ → ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => ρ n

def Term.eval (ρ : ℕ → ℝ) : Term → ℝ
  | .var n => ρ n
  | .zero => 0
  | .one => 1
  | .add a b => a.eval ρ + b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ
  | .neg a => -a.eval ρ

def Formula.Holds (ρ : ℕ → ℝ) : Formula → Prop
  | .truth b => b = true
  | .eq a b => a.eval ρ = b.eval ρ
  | .lt a b => a.eval ρ < b.eval ρ
  | .le a b => a.eval ρ ≤ b.eval ρ
  | .not p => ¬p.Holds ρ
  | .and p q => p.Holds ρ ∧ q.Holds ρ
  | .or p q => p.Holds ρ ∨ q.Holds ρ
  | .all p => ∀ x : ℝ, p.Holds (consEnv x ρ)
  | .ex p => ∃ x : ℝ, p.Holds (consEnv x ρ)

def imp (p q : Formula) : Formula := .or (.not p) q
def iffFormula (p q : Formula) : Formula := .and (imp p q) (imp q p)

@[simp] theorem holds_imp (ρ : ℕ → ℝ) (p q : Formula) :
    (imp p q).Holds ρ ↔ (p.Holds ρ → q.Holds ρ) := by
  classical
  change (¬p.Holds ρ ∨ q.Holds ρ) ↔ (p.Holds ρ → q.Holds ρ)
  constructor
  · rintro (h | h) hp
    · exact False.elim (h hp)
    · exact h
  · intro h
    by_cases hp : p.Holds ρ
    · exact Or.inr (h hp)
    · exact Or.inl hp

@[simp] theorem holds_iffFormula (ρ : ℕ → ℝ) (p q : Formula) :
    (iffFormula p q).Holds ρ ↔ (p.Holds ρ ↔ q.Holds ρ) := by
  simp only [iffFormula, Formula.Holds, holds_imp, iff_def]

abbrev Token := ℕ × ℕ
abbrev Code := List Token

def Term.code : Term → Code
  | .var n => [(0, n)]
  | .zero => [(1, 0)]
  | .one => [(2, 0)]
  | .add a b => a.code ++ b.code ++ [(3, 0)]
  | .mul a b => a.code ++ b.code ++ [(4, 0)]
  | .neg a => a.code ++ [(5, 0)]

def Formula.code : Formula → Code
  | .truth b => [(6, if b then 1 else 0)]
  | .eq a b => a.code ++ b.code ++ [(7, 0)]
  | .lt a b => a.code ++ b.code ++ [(8, 0)]
  | .le a b => a.code ++ b.code ++ [(9, 0)]
  | .not p => p.code ++ [(10, 0)]
  | .and p q => p.code ++ q.code ++ [(11, 0)]
  | .or p q => p.code ++ q.code ++ [(12, 0)]
  | .all p => p.code ++ [(13, 0)]
  | .ex p => p.code ++ [(14, 0)]

abbrev Item := Term ⊕ Formula

def step : Token → List Item → Option (List Item)
  | (0, n), s => some (.inl (.var n) :: s)
  | (1, _), s => some (.inl .zero :: s)
  | (2, _), s => some (.inl .one :: s)
  | (3, _), .inl b :: .inl a :: s => some (.inl (.add a b) :: s)
  | (4, _), .inl b :: .inl a :: s => some (.inl (.mul a b) :: s)
  | (5, _), .inl a :: s => some (.inl (.neg a) :: s)
  | (6, n), s => some (.inr (.truth (n == 1)) :: s)
  | (7, _), .inl b :: .inl a :: s => some (.inr (.eq a b) :: s)
  | (8, _), .inl b :: .inl a :: s => some (.inr (.lt a b) :: s)
  | (9, _), .inl b :: .inl a :: s => some (.inr (.le a b) :: s)
  | (10, _), .inr p :: s => some (.inr (.not p) :: s)
  | (11, _), .inr q :: .inr p :: s => some (.inr (.and p q) :: s)
  | (12, _), .inr q :: .inr p :: s => some (.inr (.or p q) :: s)
  | (13, _), .inr p :: s => some (.inr (.all p) :: s)
  | (14, _), .inr p :: s => some (.inr (.ex p) :: s)
  | _, _ => none

def run (c : Code) (s : Option (List Item)) : Option (List Item) :=
  c.foldl (fun s t => s.bind (step t)) s

theorem run_append (a b : Code) (s : Option (List Item)) :
    run (a ++ b) s = run b (run a s) := List.foldl_append

theorem run_term_code (t : Term) (s : List Item) :
    run t.code (some s) = some (.inl t :: s) := by
  induction t generalizing s with
  | var n => rfl
  | zero => rfl
  | one => rfl
  | add a b ha hb => simp only [Term.code, run_append, ha, hb]; rfl
  | mul a b ha hb => simp only [Term.code, run_append, ha, hb]; rfl
  | neg a ha => simp only [Term.code, run_append, ha]; rfl

theorem run_formula_code (p : Formula) (s : List Item) :
    run p.code (some s) = some (.inr p :: s) := by
  induction p generalizing s with
  | truth b => cases b <;> rfl
  | eq a b => simp only [Formula.code, run_append, run_term_code]; rfl
  | lt a b => simp only [Formula.code, run_append, run_term_code]; rfl
  | le a b => simp only [Formula.code, run_append, run_term_code]; rfl
  | not p hp => simp only [Formula.code, run_append, hp]; rfl
  | and p q hp hq => simp only [Formula.code, run_append, hp, hq]; rfl
  | or p q hp hq => simp only [Formula.code, run_append, hp, hq]; rfl
  | all p hp => simp only [Formula.code, run_append, hp]; rfl
  | ex p hp => simp only [Formula.code, run_append, hp]; rfl

def decode (c : Code) : Option Formula :=
  match run c (some []) with
  | some [.inr p] => some p
  | _ => none

@[simp] theorem decode_code (p : Formula) : decode p.code = some p := by
  simp only [decode, run_formula_code]

def CodeHolds (c : Code) (ρ : ℕ → ℝ) : Prop :=
  ∃ p : Formula, decode c = some p ∧ p.Holds ρ

@[simp] theorem codeHolds_code (p : Formula) (ρ : ℕ → ℝ) :
    CodeHolds p.code ρ ↔ p.Holds ρ := by
  constructor
  · rintro ⟨q, hq, h⟩
    have hpq : p = q := Option.some.inj ((decode_code p).symm.trans hq)
    rw [hpq]
    exact h
  · intro h
    exact ⟨p, decode_code p, h⟩

def termSum : ℕ → (ℕ → Term) → Term
  | 0, _ => .zero
  | n + 1, f => .add (termSum n f) (f n)

theorem eval_termSum (n : ℕ) (f : ℕ → Term) (ρ : ℕ → ℝ) :
    (termSum n f).eval ρ = ∑ i : Fin n, (f i.val).eval ρ := by
  induction n with
  | zero => simp only [termSum, Term.eval, Fin.sum_univ_zero]
  | succ n ih =>
      simp only [termSum, Term.eval, ih, Fin.sum_univ_castSucc,
        Fin.val_castSucc, Fin.val_last]

def andRange : ℕ → (ℕ → Formula) → Formula
  | 0, _ => .truth true
  | n + 1, f => .and (andRange n f) (f n)

theorem holds_andRange_nat (n : ℕ) (f : ℕ → Formula) (ρ : ℕ → ℝ) :
    (andRange n f).Holds ρ ↔ ∀ i, i < n → (f i).Holds ρ := by
  induction n with
  | zero =>
      constructor
      · intro _ i hi
        exact False.elim (Nat.not_lt_zero i hi)
      · intro _
        rfl
  | succ n ih =>
      rw [andRange, Formula.Holds, ih]
      constructor
      · rintro ⟨h, hn⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h i hi
        · exact hn
      · intro h
        exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem holds_andRange (n : ℕ) (f : ℕ → Formula) (ρ : ℕ → ℝ) :
    (andRange n f).Holds ρ ↔ ∀ i : Fin n, (f i.val).Holds ρ := by
  rw [holds_andRange_nat]
  exact ⟨fun h i => h i.val i.isLt, fun h i hi => h ⟨i, hi⟩⟩

def andList {A : Type*} (l : List A) (f : A → Formula) : Formula :=
  l.foldr (fun a p => .and (f a) p) (.truth true)

theorem holds_andList {A : Type*} (l : List A) (f : A → Formula) (ρ : ℕ → ℝ) :
    (andList l f).Holds ρ ↔ ∀ a ∈ l, (f a).Holds ρ := by
  induction l with
  | nil =>
      constructor
      · intro _ a ha
        exact False.elim (List.not_mem_nil ha)
      · intro _
        rfl
  | cons a l ih =>
      change (f a).Holds ρ ∧ (andList l f).Holds ρ ↔ _
      rw [List.forall_mem_cons]
      exact and_congr Iff.rfl ih

end Grunbaum2003.FormulaCompiler

namespace Grunbaum2003.FormulaCompiler

def extend {n : ℕ} (v : Fin n → ℝ) (ρ : ℕ → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then v ⟨i, h⟩ else ρ (i - n)

@[simp] theorem extend_zero (v : Fin 0 → ℝ) (ρ : ℕ → ℝ) : extend v ρ = ρ := by
  funext i
  simp only [extend, dif_neg (Nat.not_lt_zero i), Nat.sub_zero]

@[simp] theorem extend_fin {n : ℕ} (v : Fin n → ℝ) (ρ : ℕ → ℝ) (i : Fin n) :
    extend v ρ i.val = v i := by
  simp only [extend, dif_pos i.isLt]

@[simp] theorem extend_add {n : ℕ} (v : Fin n → ℝ) (ρ : ℕ → ℝ) (i : ℕ) :
    extend v ρ (n + i) = ρ i := by
  have hi : ¬ n + i < n := Nat.not_lt.mpr (Nat.le_add_right n i)
  simp only [extend, dif_neg hi, Nat.add_sub_cancel_left]

def snocVector {n : ℕ} (v : Fin n → ℝ) (x : ℝ) (i : Fin (n + 1)) : ℝ :=
  if h : i.val < n then v ⟨i.val, h⟩ else x

theorem snocVector_init_last {n : ℕ} (w : Fin (n + 1) → ℝ) :
    snocVector (fun i : Fin n => w i.castSucc) (w (Fin.last n)) = w := by
  funext i
  by_cases hi : i.val < n
  · simp only [snocVector, dif_pos hi]
    congr 1
  · simp only [snocVector, dif_neg hi]
    congr 1
    apply Fin.ext
    change n = i.val
    omega

theorem extend_snocVector {n : ℕ} (v : Fin n → ℝ) (x : ℝ) (ρ : ℕ → ℝ) :
    extend (snocVector v x) ρ = extend v (consEnv x ρ) := by
  funext i
  by_cases hi : i < n
  · have his : i < n + 1 := Nat.lt_succ_of_lt hi
    simp only [extend, dif_pos hi, dif_pos his, snocVector]
  · by_cases hin : i = n
    · subst i
      simp only [extend, Nat.lt_succ_self, dif_pos, snocVector, Nat.lt_irrefl,
        Nat.sub_self, consEnv]
    · have his : ¬ i < n + 1 := by omega
      have hsub : i - n = (i - (n + 1)) + 1 := by omega
      simp only [extend, dif_neg hi, dif_neg his, hsub, consEnv]

def allMany : ℕ → Formula → Formula
  | 0, p => p
  | n + 1, p => .all (allMany n p)

def exMany : ℕ → Formula → Formula
  | 0, p => p
  | n + 1, p => .ex (exMany n p)

theorem holds_allMany (n : ℕ) (p : Formula) (ρ : ℕ → ℝ) :
    (allMany n p).Holds ρ ↔ ∀ v : Fin n → ℝ, p.Holds (extend v ρ) := by
  induction n generalizing ρ with
  | zero =>
      simp only [allMany, extend_zero]
      exact ⟨fun h _ => h, fun h => h (fun _ => 0)⟩
  | succ n ih =>
      simp only [allMany, Formula.Holds, ih]
      constructor
      · intro h w
        have hw := h (w (Fin.last n)) (fun i : Fin n => w i.castSucc)
        rw [← extend_snocVector, snocVector_init_last] at hw
        exact hw
      · intro h x v
        simpa only [extend_snocVector] using h (snocVector v x)

theorem holds_exMany (n : ℕ) (p : Formula) (ρ : ℕ → ℝ) :
    (exMany n p).Holds ρ ↔ ∃ v : Fin n → ℝ, p.Holds (extend v ρ) := by
  induction n generalizing ρ with
  | zero =>
      simp only [exMany, extend_zero]
      exact ⟨fun h => ⟨fun _ => 0, h⟩, fun h => h.choose_spec⟩
  | succ n ih =>
      simp only [exMany, Formula.Holds, ih]
      constructor
      · rintro ⟨x, v, h⟩
        refine ⟨snocVector v x, ?_⟩
        simpa only [extend_snocVector] using h
      · rintro ⟨w, h⟩
        refine ⟨w (Fin.last n), fun i : Fin n => w i.castSucc, ?_⟩
        rwa [← extend_snocVector, snocVector_init_last]

end Grunbaum2003.FormulaCompiler

namespace Grunbaum2003.FormulaCompiler

private theorem primrec_binary_code {A : Type*} [Primcodable A]
    {f g : A → Code} (hf : Primrec f) (hg : Primrec g) (tag : ℕ) :
    Primrec (fun a => f a ++ g a ++ [(tag, 0)]) :=
  Primrec.list_append.comp (Primrec.list_append.comp hf hg) (Primrec.const _)

private theorem primrec_unary_code {A : Type*} [Primcodable A]
    {f : A → Code} (hf : Primrec f) (tag : ℕ) :
    Primrec (fun a => f a ++ [(tag, 0)]) :=
  Primrec.list_append.comp hf (Primrec.const _)

theorem primrec_var_code {A : Type*} [Primcodable A] {f : A → ℕ}
    (hf : Primrec f) : Primrec (fun a => (Term.var (f a)).code) :=
  Primrec.list_cons.comp ((Primrec.const 0).pair hf) (Primrec.const [])

theorem primrec_truth_code {A : Type*} [Primcodable A] {f : A → Bool}
    (hf : Primrec f) : Primrec (fun a => (Formula.truth (f a)).code) := by
  apply (Primrec.cond hf (Primrec.const [(6, 1)]) (Primrec.const [(6, 0)])).of_eq
  intro a
  cases f a <;> rfl

theorem primrec_term_add_code {A : Type*} [Primcodable A] {f g : A → Term}
    (hf : Primrec (fun a => (f a).code)) (hg : Primrec (fun a => (g a).code)) :
    Primrec (fun a => (Term.add (f a) (g a)).code) := primrec_binary_code hf hg 3

theorem primrec_term_mul_code {A : Type*} [Primcodable A] {f g : A → Term}
    (hf : Primrec (fun a => (f a).code)) (hg : Primrec (fun a => (g a).code)) :
    Primrec (fun a => (Term.mul (f a) (g a)).code) := primrec_binary_code hf hg 4

theorem primrec_term_neg_code {A : Type*} [Primcodable A] {f : A → Term}
    (hf : Primrec (fun a => (f a).code)) :
    Primrec (fun a => (Term.neg (f a)).code) := primrec_unary_code hf 5

theorem primrec_eq_code {A : Type*} [Primcodable A] {f g : A → Term}
    (hf : Primrec (fun a => (f a).code)) (hg : Primrec (fun a => (g a).code)) :
    Primrec (fun a => (Formula.eq (f a) (g a)).code) := primrec_binary_code hf hg 7

theorem primrec_lt_code {A : Type*} [Primcodable A] {f g : A → Term}
    (hf : Primrec (fun a => (f a).code)) (hg : Primrec (fun a => (g a).code)) :
    Primrec (fun a => (Formula.lt (f a) (g a)).code) := primrec_binary_code hf hg 8

theorem primrec_le_code {A : Type*} [Primcodable A] {f g : A → Term}
    (hf : Primrec (fun a => (f a).code)) (hg : Primrec (fun a => (g a).code)) :
    Primrec (fun a => (Formula.le (f a) (g a)).code) := primrec_binary_code hf hg 9

theorem primrec_not_code {A : Type*} [Primcodable A] {f : A → Formula}
    (hf : Primrec (fun a => (f a).code)) :
    Primrec (fun a => (Formula.not (f a)).code) := primrec_unary_code hf 10

theorem primrec_and_code {A : Type*} [Primcodable A] {f g : A → Formula}
    (hf : Primrec (fun a => (f a).code)) (hg : Primrec (fun a => (g a).code)) :
    Primrec (fun a => (Formula.and (f a) (g a)).code) := primrec_binary_code hf hg 11

theorem primrec_or_code {A : Type*} [Primcodable A] {f g : A → Formula}
    (hf : Primrec (fun a => (f a).code)) (hg : Primrec (fun a => (g a).code)) :
    Primrec (fun a => (Formula.or (f a) (g a)).code) := primrec_binary_code hf hg 12

theorem primrec_all_code {A : Type*} [Primcodable A] {f : A → Formula}
    (hf : Primrec (fun a => (f a).code)) :
    Primrec (fun a => (Formula.all (f a)).code) := primrec_unary_code hf 13

theorem primrec_ex_code {A : Type*} [Primcodable A] {f : A → Formula}
    (hf : Primrec (fun a => (f a).code)) :
    Primrec (fun a => (Formula.ex (f a)).code) := primrec_unary_code hf 14

theorem primrec_imp_code {A : Type*} [Primcodable A] {f g : A → Formula}
    (hf : Primrec (fun a => (f a).code)) (hg : Primrec (fun a => (g a).code)) :
    Primrec (fun a => (imp (f a) (g a)).code) :=
  primrec_or_code (primrec_not_code hf) hg

theorem primrec_iff_code {A : Type*} [Primcodable A] {f g : A → Formula}
    (hf : Primrec (fun a => (f a).code)) (hg : Primrec (fun a => (g a).code)) :
    Primrec (fun a => (iffFormula (f a) (g a)).code) :=
  primrec_and_code (primrec_imp_code hf hg) (primrec_imp_code hg hf)

theorem primrec_termSum_code {A : Type*} [Primcodable A]
    {n : A → ℕ} {f : A → ℕ → Term} (hn : Primrec n)
    (hf : Primrec (fun t : A × ℕ => (f t.1 t.2).code)) :
    Primrec (fun a => (termSum (n a) (f a)).code) := by
  have hstep : Primrec (fun t : A × (ℕ × Code) =>
      t.2.2 ++ (f t.1 t.2.1).code ++ [(3, 0)]) :=
    primrec_binary_code (Primrec.snd.comp Primrec.snd)
      (hf.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))) 3
  have hrec := Primrec.nat_rec' hn (Primrec.const [(1, 0)]) hstep.to₂
  apply hrec.of_eq
  intro a
  have h (m : ℕ) :
      Nat.rec (motive := fun _ => Code) [(1, 0)]
        (fun i s => s ++ (f a i).code ++ [(3, 0)]) m = (termSum m (f a)).code := by
    induction m with
    | zero => rfl
    | succ m ih =>
        change (Nat.rec (motive := fun _ => Code) [(1, 0)]
          (fun i s => s ++ (f a i).code ++ [(3, 0)]) m) ++ (f a m).code ++ [(3, 0)] = _
        rw [ih]
        rfl
  exact h (n a)

theorem primrec_andRange_code {A : Type*} [Primcodable A]
    {n : A → ℕ} {f : A → ℕ → Formula} (hn : Primrec n)
    (hf : Primrec (fun t : A × ℕ => (f t.1 t.2).code)) :
    Primrec (fun a => (andRange (n a) (f a)).code) := by
  have hstep : Primrec (fun t : A × (ℕ × Code) =>
      t.2.2 ++ (f t.1 t.2.1).code ++ [(11, 0)]) :=
    primrec_binary_code (Primrec.snd.comp Primrec.snd)
      (hf.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))) 11
  have hrec := Primrec.nat_rec' hn (Primrec.const [(6, 1)]) hstep.to₂
  apply hrec.of_eq
  intro a
  have h (m : ℕ) :
      Nat.rec (motive := fun _ => Code) [(6, 1)]
        (fun i s => s ++ (f a i).code ++ [(11, 0)]) m = (andRange m (f a)).code := by
    induction m with
    | zero => rfl
    | succ m ih =>
        change (Nat.rec (motive := fun _ => Code) [(6, 1)]
          (fun i s => s ++ (f a i).code ++ [(11, 0)]) m) ++ (f a m).code ++ [(11, 0)] = _
        rw [ih]
        rfl
  exact h (n a)

theorem primrec_allMany_code {A : Type*} [Primcodable A]
    {n : A → ℕ} {f : A → Formula} (hn : Primrec n)
    (hf : Primrec (fun a => (f a).code)) :
    Primrec (fun a => (allMany (n a) (f a)).code) := by
  have hstep : Primrec (fun t : A × (ℕ × Code) => t.2.2 ++ [(13, 0)]) :=
    primrec_unary_code (Primrec.snd.comp Primrec.snd) 13
  have hrec := Primrec.nat_rec' hn hf hstep.to₂
  apply hrec.of_eq
  intro a
  have h (m : ℕ) :
      Nat.rec (motive := fun _ => Code) (f a).code
        (fun _ s => s ++ [(13, 0)]) m = (allMany m (f a)).code := by
    induction m with
    | zero => rfl
    | succ m ih =>
        change (Nat.rec (motive := fun _ => Code) (f a).code
          (fun _ s => s ++ [(13, 0)]) m) ++ [(13, 0)] = _
        rw [ih]
        rfl
  exact h (n a)

theorem primrec_exMany_code {A : Type*} [Primcodable A]
    {n : A → ℕ} {f : A → Formula} (hn : Primrec n)
    (hf : Primrec (fun a => (f a).code)) :
    Primrec (fun a => (exMany (n a) (f a)).code) := by
  have hstep : Primrec (fun t : A × (ℕ × Code) => t.2.2 ++ [(14, 0)]) :=
    primrec_unary_code (Primrec.snd.comp Primrec.snd) 14
  have hrec := Primrec.nat_rec' hn hf hstep.to₂
  apply hrec.of_eq
  intro a
  have h (m : ℕ) :
      Nat.rec (motive := fun _ => Code) (f a).code
        (fun _ s => s ++ [(14, 0)]) m = (exMany m (f a)).code := by
    induction m with
    | zero => rfl
    | succ m ih =>
        change (Nat.rec (motive := fun _ => Code) (f a).code
          (fun _ s => s ++ [(14, 0)]) m) ++ [(14, 0)] = _
        rw [ih]
        rfl
  exact h (n a)

theorem primrec_andList_code {A B : Type*} [Primcodable A] [Primcodable B]
    {l : A → List B} {f : A → B → Formula} (hl : Primrec l)
    (hf : Primrec (fun t : A × B => (f t.1 t.2).code)) :
    Primrec (fun a => (andList (l a) (f a)).code) := by
  have hstep : Primrec (fun t : A × (B × Code) =>
      (f t.1 t.2.1).code ++ t.2.2 ++ [(11, 0)]) :=
    primrec_binary_code (hf.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd) 11
  have hfold := Primrec.list_foldr hl (Primrec.const [(6, 1)]) hstep.to₂
  apply hfold.of_eq
  intro a
  induction l a with
  | nil => rfl
  | cons b bs ih =>
      change (f a b).code ++
        bs.foldr (fun b s => (f a b).code ++ s ++ [(11, 0)]) [(6, 1)] ++ [(11, 0)] = _
      rw [ih]
      rfl

end Grunbaum2003.FormulaCompiler

open scoped BigOperators

namespace Grunbaum2003.FormulaCompiler

def configuration (d k : ℕ) (ρ : ℕ → ℝ) (i : Fin k) (t : Fin d) : ℝ :=
  ρ (i.val * d + t.val)

def dotTerm (d aBase vBase i : ℕ) : Term :=
  termSum d (fun t => .mul (.var (aBase + t)) (.var (vBase + i * d + t)))

theorem eval_dotTerm (d aBase vBase i : ℕ) (ρ : ℕ → ℝ) :
    (dotTerm d aBase vBase i).eval ρ =
      ∑ t : Fin d, ρ (aBase + t.val) * ρ (vBase + i * d + t.val) := by
  simp only [dotTerm, eval_termSum, Term.eval]

@[simp] theorem extend_length {n : ℕ} (v : Fin n → ℝ) (ρ : ℕ → ℝ) :
    extend v ρ n = ρ 0 := by
  simpa only [Nat.add_zero] using extend_add v ρ 0

@[simp] theorem extend_succ_add {n : ℕ} (v : Fin n → ℝ) (ρ : ℕ → ℝ) (i : ℕ) :
    extend v ρ (n + i).succ = ρ i.succ := by
  rw [← Nat.add_succ, extend_add]

def injectiveFormula (d k : ℕ) : Formula :=
  andRange k (fun i => andRange k (fun j =>
    imp (.truth (decide (i ≠ j))) (.not (andRange d (fun t =>
      .eq (.var (i * d + t)) (.var (j * d + t)))))))

theorem holds_injectiveFormula (d k : ℕ) (ρ : ℕ → ℝ) :
    (injectiveFormula d k).Holds ρ ↔ Function.Injective (configuration d k ρ) := by
  simp only [injectiveFormula, holds_andRange, holds_imp, Formula.Holds,
    decide_eq_true_eq, Term.eval]
  constructor
  · intro h i j hij
    by_contra hne
    exact h i j (fun hval => hne (Fin.ext hval)) (fun t => congrFun hij t)
  · intro h i j hne hcoords
    exact hne (congrArg Fin.val (h (funext hcoords)))

def fullSpanFormula (d k : ℕ) : Formula :=
  allMany d (exMany k (.and
    (.eq (termSum k (fun i => .var i)) .one)
    (andRange d (fun t => .eq
      (termSum k (fun i => .mul (.var i) (.var (k + d + i * d + t))))
      (.var (k + t))))))

theorem holds_fullSpanFormula (d k : ℕ) (ρ : ℕ → ℝ) :
    (fullSpanFormula d k).Holds ρ ↔
      ∀ x : Fin d → ℝ, ∃ w : Fin k → ℝ,
        (∑ i, w i) = 1 ∧ ∀ t : Fin d,
          (∑ i, w i * configuration d k ρ i t) = x t := by
  simp only [fullSpanFormula, holds_allMany, holds_exMany, Formula.Holds,
    holds_andRange, eval_termSum, Term.eval, Nat.add_assoc,
    extend_add, extend_fin, configuration]

def strictSupportFormula (d k i : ℕ) : Formula :=
  exMany d (andRange k (fun j => imp (.truth (decide (j ≠ i)))
    (.lt (dotTerm d 0 d j) (dotTerm d 0 d i))))

theorem holds_strictSupportFormula (d k : ℕ) (i : Fin k) (ρ : ℕ → ℝ) :
    (strictSupportFormula d k i.val).Holds ρ ↔
      ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * configuration d k ρ j t) <
          ∑ t, a t * configuration d k ρ i t := by
  simp only [strictSupportFormula, holds_exMany, holds_andRange, holds_imp,
    Formula.Holds, decide_eq_true_eq, eval_dotTerm, Nat.zero_add,
    Nat.add_assoc, extend_add, extend_fin, configuration, ne_eq, Fin.val_inj]

def faceSupportFormula (d k : ℕ) (J : List ℕ) : Formula :=
  .ex (exMany d (.and
    (andRange k (fun i => .le (dotTerm d 0 (d + 1) i) (.var d)))
    (andRange k (fun i => iffFormula
      (.eq (dotTerm d 0 (d + 1) i) (.var d)) (.truth (decide (i ∈ J)))))))

theorem holds_faceSupportFormula (d k : ℕ) (J : List ℕ) (ρ : ℕ → ℝ) :
    (faceSupportFormula d k J).Holds ρ ↔
      ∃ (a : Fin d → ℝ) (b : ℝ),
        (∀ i : Fin k, (∑ t, a t * configuration d k ρ i t) ≤ b) ∧
        (∀ i : Fin k, (∑ t, a t * configuration d k ρ i t) = b ↔ i.val ∈ J) := by
  simp only [faceSupportFormula, Formula.Holds, holds_exMany, holds_andRange,
    holds_iffFormula, Term.eval, eval_dotTerm, Nat.zero_add, Nat.add_assoc,
    extend_length, extend_fin, Nat.succ_add, extend_succ_add, consEnv,
    decide_eq_true_eq, configuration]
  exact exists_comm

end Grunbaum2003.FormulaCompiler

namespace Grunbaum2003.FormulaCompiler

theorem primrec_dotTerm_code {A : Type*} [Primcodable A]
    {d aBase vBase i : A → ℕ} (hd : Primrec d) (ha : Primrec aBase)
    (hv : Primrec vBase) (hi : Primrec i) :
    Primrec (fun a => (dotTerm (d a) (aBase a) (vBase a) (i a)).code) := by
  apply primrec_termSum_code hd
  apply primrec_term_mul_code
  · exact primrec_var_code (Primrec.nat_add.comp (ha.comp Primrec.fst) Primrec.snd)
  · exact primrec_var_code (Primrec.nat_add.comp
      (Primrec.nat_add.comp (hv.comp Primrec.fst)
        (Primrec.nat_mul.comp (hi.comp Primrec.fst) (hd.comp Primrec.fst))) Primrec.snd)

theorem primrec_coordinatesEq_code {A : Type*} [Primcodable A]
    {d i j : A → ℕ} (hd : Primrec d) (hi : Primrec i) (hj : Primrec j) :
    Primrec (fun a => (andRange (d a) (fun t =>
      Formula.eq (.var (i a * d a + t)) (.var (j a * d a + t)))).code) := by
  apply primrec_andRange_code hd
  apply primrec_eq_code
  · exact primrec_var_code (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (hi.comp Primrec.fst) (hd.comp Primrec.fst)) Primrec.snd)
  · exact primrec_var_code (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (hj.comp Primrec.fst) (hd.comp Primrec.fst)) Primrec.snd)

theorem primrec_injectiveFormula_code {A : Type*} [Primcodable A]
    {d k : A → ℕ} (hd : Primrec d) (hk : Primrec k) :
    Primrec (fun a => (injectiveFormula (d a) (k a)).code) := by
  apply primrec_andRange_code hk
  apply primrec_andRange_code (hk.comp Primrec.fst)
  apply primrec_imp_code
  · exact primrec_truth_code ((Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
      Primrec.snd).not.decide)
  · exact primrec_not_code (primrec_coordinatesEq_code
      (hd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem primrec_fullSpanFormula_code {A : Type*} [Primcodable A]
    {d k : A → ℕ} (hd : Primrec d) (hk : Primrec k) :
    Primrec (fun a => (fullSpanFormula (d a) (k a)).code) := by
  apply primrec_allMany_code hd
  apply primrec_exMany_code hk
  apply primrec_and_code
  · exact primrec_eq_code (primrec_termSum_code hk (primrec_var_code Primrec.snd))
      (Primrec.const Term.one.code)
  · apply primrec_andRange_code hd
    apply primrec_eq_code
    · apply primrec_termSum_code (hk.comp Primrec.fst)
      apply primrec_term_mul_code (primrec_var_code Primrec.snd)
      have hD : Primrec (fun t : (A × ℕ) × ℕ => d t.1.1) :=
        hd.comp (Primrec.fst.comp Primrec.fst)
      have hK : Primrec (fun t : (A × ℕ) × ℕ => k t.1.1) :=
        hk.comp (Primrec.fst.comp Primrec.fst)
      exact primrec_var_code (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.nat_add.comp hK hD)
          (Primrec.nat_mul.comp Primrec.snd hD)) (Primrec.snd.comp Primrec.fst))
    · exact primrec_var_code (Primrec.nat_add.comp (hk.comp Primrec.fst) Primrec.snd)

theorem primrec_strictSupportFormula_code {A : Type*} [Primcodable A]
    {d k i : A → ℕ} (hd : Primrec d) (hk : Primrec k) (hi : Primrec i) :
    Primrec (fun a => (strictSupportFormula (d a) (k a) (i a)).code) := by
  apply primrec_exMany_code hd
  apply primrec_andRange_code hk
  apply primrec_imp_code
  · exact primrec_truth_code ((Primrec.eq.comp Primrec.snd (hi.comp Primrec.fst)).not.decide)
  · exact primrec_lt_code
      (primrec_dotTerm_code (hd.comp Primrec.fst) (Primrec.const 0)
        (hd.comp Primrec.fst) Primrec.snd)
      (primrec_dotTerm_code (hd.comp Primrec.fst) (Primrec.const 0)
        (hd.comp Primrec.fst) (hi.comp Primrec.fst))

theorem primrec_faceSupportFormula_code {A : Type*} [Primcodable A]
    {d k : A → ℕ} {J : A → List ℕ}
    (hd : Primrec d) (hk : Primrec k) (hJ : Primrec J) :
    Primrec (fun a => (faceSupportFormula (d a) (k a) (J a)).code) := by
  apply primrec_ex_code
  apply primrec_exMany_code hd
  apply primrec_and_code
  · apply primrec_andRange_code hk
    exact primrec_le_code
      (primrec_dotTerm_code (hd.comp Primrec.fst) (Primrec.const 0)
        (Primrec.nat_add.comp (hd.comp Primrec.fst) (Primrec.const 1)) Primrec.snd)
      (primrec_var_code (hd.comp Primrec.fst))
  · apply primrec_andRange_code hk
    apply primrec_iff_code
    · exact primrec_eq_code
        (primrec_dotTerm_code (hd.comp Primrec.fst) (Primrec.const 0)
          (Primrec.nat_add.comp (hd.comp Primrec.fst) (Primrec.const 1)) Primrec.snd)
        (primrec_var_code (hd.comp Primrec.fst))
    · exact primrec_truth_code
        ((Grunbaum2003.primrec_list_mem.comp Primrec.snd (hJ.comp Primrec.fst)).decide)

end Grunbaum2003.FormulaCompiler

open scoped BigOperators

namespace Grunbaum2003.FormulaCompiler

def rowOccurs (S : List (List ℕ)) (J : List ℕ) : Bool :=
  decide (∃ L ∈ S, L.toFinset = J.toFinset)

def properRow (k : ℕ) (J : List ℕ) : Bool :=
  decide (J.toFinset.Nonempty ∧ J.toFinset ≠ Finset.range k)

def boundedRows (k : ℕ) (S : List (List ℕ)) : Bool :=
  decide (∀ L ∈ S, ∀ n ∈ L, n < k)

def facesFormula (d k : ℕ) (S : List (List ℕ)) : Formula :=
  andList ((List.range k).sublists') (fun J =>
    iffFormula (.truth (rowOccurs S J))
      (.and (.truth (properRow k J)) (faceSupportFormula d k J)))

theorem holds_facesFormula (d k : ℕ) (S : List (List ℕ)) (ρ : ℕ → ℝ) :
    (facesFormula d k S).Holds ρ ↔
      ∀ J ∈ (Finset.range k).powerset,
        (∃ L ∈ S, L.toFinset = J) ↔
          J.Nonempty ∧ J ≠ Finset.range k ∧
            ∃ (a : Fin d → ℝ) (b : ℝ),
              (∀ i : Fin k, (∑ t, a t * configuration d k ρ i t) ≤ b) ∧
              (∀ i : Fin k, (∑ t, a t * configuration d k ρ i t) = b ↔ i.val ∈ J) := by
  have hAt (R : List ℕ) :
      (iffFormula (.truth (rowOccurs S R))
        (.and (.truth (properRow k R)) (faceSupportFormula d k R))).Holds ρ ↔
        ((∃ L ∈ S, L.toFinset = R.toFinset) ↔
          R.toFinset.Nonempty ∧ R.toFinset ≠ Finset.range k ∧
            ∃ (a : Fin d → ℝ) (b : ℝ),
              (∀ i : Fin k, (∑ t, a t * configuration d k ρ i t) ≤ b) ∧
              (∀ i : Fin k, (∑ t, a t * configuration d k ρ i t) = b ↔
                i.val ∈ R.toFinset)) := by
    simp only [holds_iffFormula, Formula.Holds, rowOccurs, properRow,
      decide_eq_true_eq, holds_faceSupportFormula, List.mem_toFinset, and_assoc]
  rw [facesFormula, holds_andList]
  constructor
  · intro h J hJ
    have hJsub : J ⊆ Finset.range k := Finset.mem_powerset.mp hJ
    let R := (List.range k).filter (fun n => n ∈ J)
    have hRset : R.toFinset = J := by
      ext n
      simp only [R, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨And.right, fun hn => ⟨Finset.mem_range.mp (hJsub hn), hn⟩⟩
    have hRmem : R ∈ (List.range k).sublists' := List.mem_sublists'.mpr List.filter_sublist
    simpa only [hRset] using (hAt R).mp (h R hRmem)
  · intro h R hR
    have hRsub := List.mem_sublists'.mp hR
    have hRset : R.toFinset ⊆ Finset.range k := by
      intro n hn
      exact Finset.mem_range.mpr (List.mem_range.mp
        (hRsub.subset (List.mem_toFinset.mp hn)))
    exact (hAt R).mpr (h R.toFinset (Finset.mem_powerset.mpr hRset))

def certificateBody (d k : ℕ) (S : List (List ℕ)) : Formula :=
  .and (.truth (decide (0 < k)))
    (.and (injectiveFormula d k)
      (.and (fullSpanFormula d k)
        (.and (andRange k (fun i => strictSupportFormula d k i))
          (.and (.truth (boundedRows k S)) (facesFormula d k S)))))

theorem holds_certificateBody (d k : ℕ) (S : List (List ℕ)) (ρ : ℕ → ℝ) :
    (certificateBody d k S).Holds ρ ↔
      0 < k ∧ Function.Injective (configuration d k ρ) ∧
      (∀ x : Fin d → ℝ, ∃ w : Fin k → ℝ,
        (∑ i, w i) = 1 ∧ ∀ t : Fin d,
          (∑ i, w i * configuration d k ρ i t) = x t) ∧
      (∀ i : Fin k, ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * configuration d k ρ j t) < ∑ t, a t * configuration d k ρ i t) ∧
      (∀ L ∈ S, ∀ n ∈ L, n < k) ∧
      ∀ J ∈ (Finset.range k).powerset,
        (∃ L ∈ S, L.toFinset = J) ↔
          J.Nonempty ∧ J ≠ Finset.range k ∧
            ∃ (a : Fin d → ℝ) (b : ℝ),
              (∀ i : Fin k, (∑ t, a t * configuration d k ρ i t) ≤ b) ∧
              (∀ i : Fin k, (∑ t, a t * configuration d k ρ i t) = b ↔ i.val ∈ J) := by
  simp only [certificateBody, Formula.Holds, decide_eq_true_eq,
    holds_injectiveFormula, holds_fullSpanFormula, holds_andRange,
    holds_strictSupportFormula, boundedRows, holds_facesFormula]

def compileFormula (d k : ℕ) (S : List (List ℕ)) : Formula :=
  exMany (k * d) (certificateBody d k S)

def compile (d k : ℕ) (S : List (List ℕ)) : Code := (compileFormula d k S).code

theorem configuration_extend {d k : ℕ} (v : Fin (k * d) → ℝ) (ρ : ℕ → ℝ)
    (i : Fin k) (t : Fin d) :
    configuration d k (extend v ρ) i t = v (finProdFinEquiv (i, t)) := by
  have hidx : (finProdFinEquiv (i, t)).val = i.val * d + t.val := by
    change t.val + d * i.val = i.val * d + t.val
    ac_rfl
  change extend v ρ (i.val * d + t.val) = _
  rw [← hidx]
  exact extend_fin v ρ (finProdFinEquiv (i, t))

theorem codeHolds_compile_iff (d k : ℕ) (S : List (List ℕ)) (ρ : ℕ → ℝ) :
    CodeHolds (compile d k S) ρ ↔
      ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P := by
  rw [compile, codeHolds_code, compileFormula, holds_exMany,
    auto_GRU_M05_EFFECTIVE_TYPES_exists_schemeRealizes_iff_arithmetic_certificates]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨configuration d k (extend v ρ),
      (holds_certificateBody d k S (extend v ρ)).mp hv⟩
  · rintro ⟨V, hV⟩
    let v : Fin (k * d) → ℝ := fun u =>
      V (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2
    have hconfig : configuration d k (extend v ρ) = V := by
      funext i t
      rw [configuration_extend]
      simp only [v, Equiv.symm_apply_apply]
    refine ⟨v, (holds_certificateBody d k S (extend v ρ)).mpr ?_⟩
    simpa only [hconfig] using hV

end Grunbaum2003.FormulaCompiler

namespace Grunbaum2003.FormulaCompiler

private theorem primrec_list_subset : PrimrecRel (fun A B : List ℕ => A ⊆ B) :=
  PrimrecRel.of_eq Grunbaum2003.primrec_list_mem.forall_mem_list (by intro A B; rfl)

private theorem primrec_rowSetEq : PrimrecRel (fun A B : List ℕ => A.toFinset = B.toFinset) := by
  have hBoth : PrimrecRel (fun A B : List ℕ => A ⊆ B ∧ B ⊆ A) := by
    change PrimrecPred (fun p : List ℕ × List ℕ => p.1 ⊆ p.2 ∧ p.2 ⊆ p.1)
    exact primrec_list_subset.and primrec_list_subset.swap
  apply PrimrecRel.of_eq hBoth
  intro A B
  constructor
  · rintro ⟨hAB, hBA⟩
    apply Finset.Subset.antisymm
    · intro n hn
      exact List.mem_toFinset.mpr (hAB (List.mem_toFinset.mp hn))
    · intro n hn
      exact List.mem_toFinset.mpr (hBA (List.mem_toFinset.mp hn))
  · intro h
    constructor
    · intro n hn
      have hn' : n ∈ A.toFinset := List.mem_toFinset.mpr hn
      rw [h] at hn'
      exact List.mem_toFinset.mp hn'
    · intro n hn
      have hn' : n ∈ B.toFinset := List.mem_toFinset.mpr hn
      rw [← h] at hn'
      exact List.mem_toFinset.mp hn'

theorem primrec_rowOccurs {A : Type*} [Primcodable A]
    {S : A → List (List ℕ)} {J : A → List ℕ} (hS : Primrec S) (hJ : Primrec J) :
    Primrec (fun a => rowOccurs (S a) (J a)) :=
  (primrec_rowSetEq.exists_mem_list.comp hS hJ).decide

theorem primrec_properRow {A : Type*} [Primcodable A]
    {k : A → ℕ} {J : A → List ℕ} (hk : Primrec k) (hJ : Primrec J) :
    Primrec (fun a => properRow (k a) (J a)) := by
  have hNonempty : PrimrecPred (fun a => J a ≠ []) :=
    (Primrec.eq.comp hJ (Primrec.const [])).not
  have hFull : PrimrecPred (fun a => (J a).toFinset = (List.range (k a)).toFinset) :=
    primrec_rowSetEq.comp hJ (Primrec.list_range.comp hk)
  have hProper : PrimrecPred (fun a =>
      (J a).toFinset.Nonempty ∧ (J a).toFinset ≠ Finset.range (k a)) := by
    apply (hNonempty.and hFull.not).of_eq
    intro a
    simp only [List.toFinset_nonempty_iff, List.toFinset_range]
  exact hProper.decide

theorem primrec_boundedRows {A : Type*} [Primcodable A]
    {k : A → ℕ} {S : A → List (List ℕ)} (hk : Primrec k) (hS : Primrec S) :
    Primrec (fun a => boundedRows (k a) (S a)) := by
  have h : PrimrecPred (fun a => ∀ L ∈ S a, ∀ n ∈ L, n < k a) := by
    exact Primrec.nat_lt.forall_mem_list.forall_mem_list.comp hS hk
  exact h.decide

theorem primrec_facesFormula_code {A : Type*} [Primcodable A]
    {d k : A → ℕ} {S : A → List (List ℕ)}
    (hd : Primrec d) (hk : Primrec k) (hS : Primrec S) :
    Primrec (fun a => (facesFormula (d a) (k a) (S a)).code) := by
  apply primrec_andList_code
    (Grunbaum2003.primrec_list_sublists.comp (Primrec.list_range.comp hk))
  apply primrec_iff_code
  · exact primrec_truth_code (primrec_rowOccurs (hS.comp Primrec.fst) Primrec.snd)
  · apply primrec_and_code
    · exact primrec_truth_code (primrec_properRow (hk.comp Primrec.fst) Primrec.snd)
    · exact primrec_faceSupportFormula_code (hd.comp Primrec.fst)
        (hk.comp Primrec.fst) Primrec.snd

theorem primrec_certificateBody_code {A : Type*} [Primcodable A]
    {d k : A → ℕ} {S : A → List (List ℕ)}
    (hd : Primrec d) (hk : Primrec k) (hS : Primrec S) :
    Primrec (fun a => (certificateBody (d a) (k a) (S a)).code) := by
  apply primrec_and_code
  · exact primrec_truth_code ((Primrec.nat_lt.comp (Primrec.const 0) hk).decide)
  · apply primrec_and_code (primrec_injectiveFormula_code hd hk)
    apply primrec_and_code (primrec_fullSpanFormula_code hd hk)
    apply primrec_and_code
    · exact primrec_andRange_code hk
        (primrec_strictSupportFormula_code (hd.comp Primrec.fst)
          (hk.comp Primrec.fst) Primrec.snd)
    · exact primrec_and_code (primrec_truth_code (primrec_boundedRows hk hS))
        (primrec_facesFormula_code hd hk hS)

theorem primrec_compile :
    Primrec (fun z : (ℕ × ℕ) × List (List ℕ) => compile z.1.1 z.1.2 z.2) := by
  apply primrec_exMany_code
    (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
  exact primrec_certificateBody_code (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst) Primrec.snd

theorem computable_compile :
    Computable (fun z : (ℕ × ℕ) × List (List ℕ) => compile z.1.1 z.1.2 z.2) :=
  primrec_compile.to_comp

end Grunbaum2003.FormulaCompiler

namespace Grunbaum2003.FormulaCompiler.Parametric

abbrev TermPoly := List Term

def add : TermPoly → TermPoly → TermPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => .add a b :: add p q

def scale (a : Term) (p : TermPoly) : TermPoly := p.map (.mul a)

def mul : TermPoly → TermPoly → TermPoly
  | [], _ => []
  | a :: p, q => add (scale a q) (.zero :: mul p q)

def neg (p : TermPoly) : TermPoly := p.map Term.neg

def abstract0 : Term → TermPoly
  | .var 0 => [.zero, .one]
  | .var (n + 1) => [.var n]
  | .zero => []
  | .one => [.one]
  | .add a b => add (abstract0 a) (abstract0 b)
  | .mul a b => mul (abstract0 a) (abstract0 b)
  | .neg a => neg (abstract0 a)

def horner (ρ : ℕ → ℝ) (x : ℝ) : TermPoly → ℝ
  | [] => 0
  | a :: p => a.eval ρ + x * horner ρ x p

theorem horner_add (ρ : ℕ → ℝ) (x : ℝ) (p q : TermPoly) :
    horner ρ x (add p q) = horner ρ x p + horner ρ x q := by
  induction p generalizing q with
  | nil => simp only [add, horner, zero_add]
  | cons a p ih =>
      cases q with
      | nil => simp only [add, horner, add_zero]
      | cons b q => simp only [add, horner, Term.eval, ih]; ring

theorem horner_scale (ρ : ℕ → ℝ) (x : ℝ) (a : Term) (p : TermPoly) :
    horner ρ x (scale a p) = a.eval ρ * horner ρ x p := by
  induction p with
  | nil => simp only [scale, List.map_nil, horner, mul_zero]
  | cons b p ih =>
      change a.eval ρ * b.eval ρ + x * horner ρ x (scale a p) =
        a.eval ρ * (b.eval ρ + x * horner ρ x p)
      rw [ih]
      ring

theorem horner_mul (ρ : ℕ → ℝ) (x : ℝ) (p q : TermPoly) :
    horner ρ x (mul p q) = horner ρ x p * horner ρ x q := by
  induction p with
  | nil => simp only [mul, horner, zero_mul]
  | cons a p ih =>
      rw [mul, horner_add, horner_scale]
      simp only [horner, Term.eval, ih]
      ring

theorem horner_neg (ρ : ℕ → ℝ) (x : ℝ) (p : TermPoly) :
    horner ρ x (neg p) = -horner ρ x p := by
  induction p with
  | nil => simp only [neg, List.map_nil, horner, neg_zero]
  | cons a p ih =>
      change -a.eval ρ + x * horner ρ x (neg p) = -(a.eval ρ + x * horner ρ x p)
      rw [ih]
      ring

theorem horner_abstract0 (t : Term) (ρ : ℕ → ℝ) (x : ℝ) :
    horner ρ x (abstract0 t) = t.eval (consEnv x ρ) := by
  induction t with
  | var n => cases n <;> simp [abstract0, horner, Term.eval, consEnv]
  | zero => rfl
  | one => simp only [abstract0, horner, Term.eval, mul_zero, add_zero]
  | add a b ha hb => rw [abstract0, horner_add, ha, hb]; rfl
  | mul a b ha hb => rw [abstract0, horner_mul, ha, hb]; rfl
  | neg a ha => rw [abstract0, horner_neg, ha]; rfl

noncomputable def specialize (ρ : ℕ → ℝ) : TermPoly → Polynomial ℝ
  | [] => 0
  | a :: p => Polynomial.C (a.eval ρ) + specialize ρ p * Polynomial.X

theorem eval_specialize (p : TermPoly) (ρ : ℕ → ℝ) (x : ℝ) :
    Polynomial.eval x (specialize ρ p) = horner ρ x p := by
  induction p with
  | nil => simp only [specialize, Polynomial.eval_zero, horner]
  | cons a p ih =>
      simp only [specialize, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X, ih, horner]
      ring

theorem eval_specialize_abstract0 (t : Term) (ρ : ℕ → ℝ) (x : ℝ) :
    Polynomial.eval x (specialize ρ (abstract0 t)) = t.eval (consEnv x ρ) :=
  (eval_specialize _ _ _).trans (horner_abstract0 _ _ _)

def coefficient (p : TermPoly) (n : ℕ) : Term := (p[n]?).getD .zero

theorem coeff_specialize (p : TermPoly) (ρ : ℕ → ℝ) (n : ℕ) :
    (specialize ρ p).coeff n = (coefficient p n).eval ρ := by
  induction p generalizing n with
  | nil => cases n <;> simp [specialize, coefficient, Term.eval]
  | cons a p ih =>
      cases n with
      | zero => simp [specialize, coefficient]
      | succ n =>
          simp only [specialize, Polynomial.coeff_add, Polynomial.coeff_C,
            Nat.succ_ne_zero, ↓reduceIte, Polynomial.coeff_mul_X, zero_add]
          simpa only [coefficient, List.getElem?_cons_succ] using ih n

noncomputable def specializedSize (ρ : ℕ → ℝ) (p : TermPoly) : ℕ := by
  classical
  exact if specialize ρ p = 0 then 0 else (specialize ρ p).natDegree + 1

private theorem specialize_cons_natDegree (ρ : ℕ → ℝ) (a : Term) (p : TermPoly)
    (hp : specialize ρ p ≠ 0) :
    (specialize ρ (a :: p)).natDegree = (specialize ρ p).natDegree + 1 := by
  rw [specialize, add_comm, Polynomial.natDegree_add_C, Polynomial.natDegree_mul_X hp]

private theorem specialize_cons_ne_zero (ρ : ℕ → ℝ) (a : Term) (p : TermPoly)
    (hp : specialize ρ p ≠ 0) : specialize ρ (a :: p) ≠ 0 := by
  intro hz
  have h := specialize_cons_natDegree ρ a p hp
  rw [hz, Polynomial.natDegree_zero] at h
  omega

private theorem specializedSize_cons_of_ne_zero (ρ : ℕ → ℝ) (a : Term) (p : TermPoly)
    (hp : specialize ρ p ≠ 0) :
    specializedSize ρ (a :: p) = specializedSize ρ p + 1 := by
  classical
  rw [specializedSize, if_neg (specialize_cons_ne_zero ρ a p hp),
    specialize_cons_natDegree ρ a p hp, specializedSize, if_neg hp]

def branch (test yes no : Formula) : Formula :=
  .or (.and test yes) (.and (.not test) no)

theorem holds_branch (test yes no : Formula) (ρ : ℕ → ℝ) :
    (branch test yes no).Holds ρ ↔
      (test.Holds ρ ∧ yes.Holds ρ) ∨ (¬test.Holds ρ ∧ no.Holds ρ) := Iff.rfl

def sizeCases : TermPoly → (ℕ → Formula) → Formula
  | [], k => k 0
  | a :: p, k => sizeCases p (fun n => if n = 0 then
      branch (.eq a .zero) (k 0) (k 1) else k (n + 1))

theorem holds_sizeCases (p : TermPoly) (k : ℕ → Formula) (ρ : ℕ → ℝ) :
    (sizeCases p k).Holds ρ ↔ (k (specializedSize ρ p)).Holds ρ := by
  classical
  induction p generalizing k with
  | nil => simp only [sizeCases, specializedSize, specialize, ↓reduceIte]
  | cons a p ih =>
      rw [sizeCases, ih]
      by_cases hp : specialize ρ p = 0
      · have hs : specializedSize ρ p = 0 := by simp only [specializedSize, hp, ↓reduceIte]
        rw [hs, if_pos rfl, holds_branch]
        by_cases ha : a.eval ρ = 0
        · have hcons : specialize ρ (a :: p) = 0 := by simp only [specialize, hp, ha, Polynomial.C_0, zero_mul, add_zero]
          simp only [Formula.Holds, Term.eval, ha, true_and, not_true_eq_false,
            false_and, or_false, specializedSize, hcons, ↓reduceIte]
        · have hcons : specialize ρ (a :: p) = Polynomial.C (a.eval ρ) := by
            simp only [specialize, hp, zero_mul, add_zero]
          simp only [Formula.Holds, Term.eval, ha, false_and, not_false_eq_true,
            true_and, false_or, specializedSize, hcons, Polynomial.C_eq_zero,
            ↓reduceIte, Polynomial.natDegree_C, zero_add]
      · have hs : specializedSize ρ p ≠ 0 := by
          simp only [specializedSize, if_neg hp, ne_eq, Nat.add_eq_zero_iff,
            one_ne_zero, and_false, not_false_eq_true]
        rw [if_neg hs, specializedSize_cons_of_ne_zero ρ a p hp]

def leadingCases (p : TermPoly) (k : Term → Formula) : Formula :=
  sizeCases p (fun n => k (if n = 0 then .zero else coefficient p (n - 1)))

theorem eval_leading_selected (p : TermPoly) (ρ : ℕ → ℝ) :
    (if specializedSize ρ p = 0 then Term.zero else
      coefficient p (specializedSize ρ p - 1)).eval ρ =
        (specialize ρ p).leadingCoeff := by
  classical
  by_cases hp : specialize ρ p = 0
  · simp only [specializedSize, hp, ↓reduceIte, Term.eval, Polynomial.leadingCoeff_zero]
  · simp only [specializedSize, if_neg hp, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, ↓reduceIte, Nat.add_sub_cancel]
    exact (coeff_specialize p ρ _).symm.trans Polynomial.coeff_natDegree

theorem holds_leadingCases (p : TermPoly) (k : Term → Formula) (ρ : ℕ → ℝ)
    (P : ℝ → Prop) (hk : ∀ t, (k t).Holds ρ ↔ P (t.eval ρ)) :
    (leadingCases p k).Holds ρ ↔ P (specialize ρ p).leadingCoeff := by
  rw [leadingCases, holds_sizeCases, hk, eval_leading_selected]

theorem holds_leading_pos (p : TermPoly) (ρ : ℕ → ℝ) :
    (leadingCases p (fun t => .lt .zero t)).Holds ρ ↔
      0 < (specialize ρ p).leadingCoeff := by
  apply holds_leadingCases p _ ρ (fun x => 0 < x)
  intro t
  rfl

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

abbrev PolyCode := List Code

private def binaryCode (tag : ℕ) (a b : Code) : Code := a ++ b ++ [(tag, 0)]
private def unaryCode (tag : ℕ) (a : Code) : Code := a ++ [(tag, 0)]

private theorem primrec_binaryCode {A : Type*} [Primcodable A]
    (tag : ℕ) {f g : A → Code} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => binaryCode tag (f a) (g a)) :=
  Primrec.list_append.comp (Primrec.list_append.comp hf hg) (Primrec.const _)

private theorem primrec_unaryCode {A : Type*} [Primcodable A]
    (tag : ℕ) {f : A → Code} (hf : Primrec f) :
    Primrec (fun a => unaryCode tag (f a)) :=
  Primrec.list_append.comp hf (Primrec.const _)

private def branchCode (test yes no : Code) : Code :=
  binaryCode 12 (binaryCode 11 test yes) (binaryCode 11 (unaryCode 10 test) no)

private theorem primrec_branchCode {A : Type*} [Primcodable A]
    {f g h : A → Code} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun a => branchCode (f a) (g a) (h a)) :=
  primrec_binaryCode 12 (primrec_binaryCode 11 hf hg)
    (primrec_binaryCode 11 (primrec_unaryCode 10 hf) hh)

def sizeTableStep (c : Code) (table : PolyCode) : PolyCode :=
  branchCode (binaryCode 7 c Term.zero.code)
    (table.getD 0 (Formula.truth false).code)
    (table.getD 1 (Formula.truth false).code) :: table.drop 2

def sizeTableCode (p table : PolyCode) : Code :=
  (p.foldl (fun table c => sizeTableStep c table) table).getD 0
    (Formula.truth false).code

theorem primrec_sizeTableStep : Primrec₂ sizeTableStep :=
  Primrec.list_cons.comp
    (primrec_branchCode (primrec_binaryCode 7 Primrec.fst (Primrec.const _))
      ((Primrec.list_getD _).comp Primrec.snd (Primrec.const 0))
      ((Primrec.list_getD _).comp Primrec.snd (Primrec.const 1)))
    (Primrec.list_drop.comp (Primrec.const 2) Primrec.snd)

theorem primrec_sizeTableCode : Primrec₂ sizeTableCode := by
  have hfold : Primrec (fun z : PolyCode × PolyCode =>
      z.1.foldl (fun table c => sizeTableStep c table) z.2) :=
    Primrec.list_foldl Primrec.fst Primrec.snd
      (primrec_sizeTableStep.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd)).to₂
  exact (Primrec.list_getD _).comp hfold (Primrec.const 0)

private theorem sizeTableStep_range (a : Term) (k : ℕ → Formula) (n : ℕ) :
    sizeTableStep a.code ((List.range (n + 2)).map (fun i => (k i).code)) =
      (List.range (n + 1)).map (fun i =>
        (if i = 0 then branch (.eq a .zero) (k 0) (k 1) else k (i + 1)).code) := by
  simp [sizeTableStep, List.range_succ_eq_map, List.map_map, branchCode,
    binaryCode, unaryCode, branch, Formula.code]

theorem sizeTableCode_eq (p : TermPoly) (k : ℕ → Formula) :
    sizeTableCode (p.map Term.code)
      ((List.range (p.length + 1)).map (fun i => (k i).code)) =
        (sizeCases p k).code := by
  induction p generalizing k with
  | nil => simp [sizeTableCode, sizeCases]
  | cons a p ih =>
      change ((p.map Term.code).foldl (fun table c => sizeTableStep c table)
        (sizeTableStep a.code ((List.range (p.length + 2)).map
          (fun i => (k i).code)))).getD 0 (Formula.truth false).code = _
      rw [sizeTableStep_range]
      exact ih (fun i => if i = 0 then branch (.eq a .zero) (k 0) (k 1) else k (i + 1))

theorem primrec_sizeCases_code {A : Type*} [Primcodable A]
    {p : A → TermPoly} {k : A → ℕ → Formula}
    (hp : Primrec (fun a => (p a).map Term.code))
    (hk : Primrec (fun z : A × ℕ => (k z.1 z.2).code)) :
    Primrec (fun a => (sizeCases (p a) (k a)).code) := by
  have hlen : Primrec (fun a => (p a).length + 1) :=
    (Primrec.nat_add.comp (Primrec.list_length.comp hp) (Primrec.const 1)).of_eq
      (fun a => by rw [List.length_map])
  have htable : Primrec (fun a =>
      (List.range ((p a).length + 1)).map (fun i => (k a i).code)) :=
    Primrec.list_map (Primrec.list_range.comp hlen) hk.to₂
  exact (primrec_sizeTableCode.comp hp htable).of_eq (fun a => sizeTableCode_eq (p a) (k a))

theorem coefficient_code (p : TermPoly) (n : ℕ) :
    ((p.map Term.code).getD n Term.zero.code) = (coefficient p n).code := by
  induction p generalizing n with
  | nil => cases n <;> rfl
  | cons a p ih => cases n with
    | zero => rfl
    | succ n => exact ih n

theorem primrec_leading_pos_code {A : Type*} [Primcodable A]
    {p : A → TermPoly} (hp : Primrec (fun a => (p a).map Term.code)) :
    Primrec (fun a => (leadingCases (p a) (fun t => .lt .zero t)).code) := by
  apply primrec_sizeCases_code hp
  apply primrec_lt_code (Primrec.const Term.zero.code)
  have hcoeff : Primrec (fun z : A × ℕ =>
      (coefficient (p z.1) (z.2 - 1)).code) :=
    ((Primrec.list_getD Term.zero.code).comp (hp.comp Primrec.fst)
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))).of_eq
        (fun z => coefficient_code (p z.1) (z.2 - 1))
  apply (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.const Term.zero.code) hcoeff).of_eq
  intro z
  by_cases hz : z.2 = 0 <;> simp only [hz, ↓reduceIte]

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

private def appendOp (tag : ℕ) (a b : Code) : Code := a ++ b ++ [(tag, 0)]

private theorem primrec_appendOp {A : Type*} [Primcodable A]
    (tag : ℕ) {f g : A → Code} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => appendOp tag (f a) (g a)) :=
  Primrec.list_append.comp (Primrec.list_append.comp hf hg) (Primrec.const _)

private theorem zipWithAll_range {α β γ : Type*} (f : Option α → Option β → γ)
    (p : List α) (q : List β) :
    List.zipWithAll f p q = (List.range (max p.length q.length)).map
      (fun i => f p[i]? q[i]?) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_zipWithAll, List.getElem?_map]
  by_cases hi : i < max p.length q.length
  · rw [List.getElem?_range hi, Option.map_some]
    cases hp : p[i]? <;> cases hq : q[i]? <;> try rfl
    have hp' := List.getElem?_eq_none_iff.mp hp
    have hq' := List.getElem?_eq_none_iff.mp hq
    omega
  · have hp : p[i]? = none := List.getElem?_eq_none (by omega)
    have hq : q[i]? = none := List.getElem?_eq_none (by omega)
    rw [hp, hq, List.getElem?_eq_none (by simpa only [List.length_range] using Nat.le_of_not_gt hi)]
    rfl

private theorem primrec_zipWithAll {α β γ : Type*}
    [Primcodable α] [Primcodable β] [Primcodable γ]
    (f : Option α → Option β → γ) (hf : Primrec₂ f) :
    Primrec₂ (List.zipWithAll f) := by
  have hlen : Primrec (fun z : List α × List β => max z.1.length z.2.length) :=
    Primrec.nat_max.comp (Primrec.list_length.comp Primrec.fst)
      (Primrec.list_length.comp Primrec.snd)
  have helem : Primrec (fun z : (List α × List β) × ℕ =>
      f z.1.1[z.2]? z.1.2[z.2]?) :=
    hf.comp (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact (Primrec.list_map (Primrec.list_range.comp hlen) helem.to₂).of_eq
    (fun z => (zipWithAll_range f z.1 z.2).symm)

private def addPair : Option Code → Option Code → Code
  | none, none => Term.zero.code
  | none, some b => b
  | some a, none => a
  | some a, some b => appendOp 3 a b

def addCodes (p q : PolyCode) : PolyCode := List.zipWithAll addPair p q
def scaleCodes (a : Code) (p : PolyCode) : PolyCode := p.map (appendOp 4 a)
def negCodes (p : PolyCode) : PolyCode := p.map (fun a => a ++ [(5, 0)])
def mulCodes (p q : PolyCode) : PolyCode :=
  p.foldr (fun a rest => addCodes (scaleCodes a q) (Term.zero.code :: rest)) []

private theorem primrec_addPair : Primrec₂ addPair := by
  have hnone : Primrec (fun z : Option Code × Option Code => z.2.getD Term.zero.code) :=
    Primrec.option_getD.comp Primrec.snd (Primrec.const _)
  have hsome : Primrec (fun z : (Option Code × Option Code) × Code =>
      Option.casesOn (motive := fun _ : Option Code => Code)
        z.1.2 z.2 (fun b => appendOp 3 z.2 b)) :=
    Primrec.option_casesOn (Primrec.snd.comp Primrec.fst) Primrec.snd
      (primrec_appendOp 3 (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  apply (Primrec.option_casesOn Primrec.fst hnone hsome.to₂).of_eq
  intro z
  rcases z with ⟨a, b⟩
  cases a <;> cases b <;> rfl

theorem primrec_addCodes : Primrec₂ addCodes := primrec_zipWithAll addPair primrec_addPair

theorem primrec_scaleCodes : Primrec₂ scaleCodes :=
  Primrec.list_map Primrec.snd
    (primrec_appendOp 4 (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem primrec_negCodes : Primrec negCodes :=
  Primrec.list_map Primrec.id
    (Primrec.list_append.comp Primrec.snd (Primrec.const [(5, 0)])).to₂

theorem primrec_mulCodes : Primrec₂ mulCodes :=
  Primrec.list_foldr Primrec.fst (Primrec.const [])
    (primrec_addCodes.comp
      (primrec_scaleCodes.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.const Term.zero.code) (Primrec.snd.comp Primrec.snd))).to₂

theorem addCodes_map (p q : TermPoly) :
    addCodes (p.map Term.code) (q.map Term.code) = (add p q).map Term.code := by
  induction p generalizing q with
  | nil => simp [addCodes, addPair, add]
  | cons a p ih =>
      cases q with
      | nil => simp [addCodes, addPair, add]
      | cons b q =>
          change appendOp 3 a.code b.code :: addCodes (p.map Term.code) (q.map Term.code) = _
          rw [ih]
          rfl

theorem scaleCodes_map (a : Term) (p : TermPoly) :
    scaleCodes a.code (p.map Term.code) = (scale a p).map Term.code := by
  induction p with
  | nil => rfl
  | cons b p ih =>
      change appendOp 4 a.code b.code :: scaleCodes a.code (p.map Term.code) = _
      rw [ih]
      rfl

theorem negCodes_map (p : TermPoly) : negCodes (p.map Term.code) = (neg p).map Term.code := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change (a.code ++ [(5, 0)]) :: negCodes (p.map Term.code) = _
      rw [ih]
      rfl

theorem mulCodes_map (p q : TermPoly) :
    mulCodes (p.map Term.code) (q.map Term.code) = (mul p q).map Term.code := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change addCodes (scaleCodes a.code (q.map Term.code))
        (Term.zero.code :: mulCodes (p.map Term.code) (q.map Term.code)) = _
      rw [scaleCodes_map, ih]
      exact addCodes_map (scale a q) (.zero :: mul p q)

private def binaryStack (op : PolyCode → PolyCode → PolyCode) : List PolyCode → List PolyCode
  | b :: a :: rest => op a b :: rest
  | _ => []

private def unaryStack (op : PolyCode → PolyCode) : List PolyCode → List PolyCode
  | a :: rest => op a :: rest
  | _ => []

private theorem primrec_binaryStack {op : PolyCode → PolyCode → PolyCode}
    (hop : Primrec₂ op) : Primrec (binaryStack op) := by
  have h := Primrec.ite (Primrec.nat_le.comp (Primrec.const 2) Primrec.list_length)
    (Primrec.list_cons.comp
      (hop.comp ((Primrec.list_getD []).comp Primrec.id (Primrec.const 1))
        ((Primrec.list_getD []).comp Primrec.id (Primrec.const 0)))
      (Primrec.list_drop.comp (Primrec.const 2) Primrec.id)) (Primrec.const [])
  apply h.of_eq
  intro s
  cases s with
  | nil => rfl
  | cons b s => cases s <;> rfl

private theorem primrec_unaryStack {op : PolyCode → PolyCode}
    (hop : Primrec op) : Primrec (unaryStack op) := by
  apply (Primrec.list_casesOn Primrec.id (Primrec.const [])
    (Primrec.list_cons.comp (hop.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro s
  cases s <;> rfl

def abstractStep (t : Token) (s : List PolyCode) : List PolyCode :=
  if t.1 = 0 then
    (if t.2 = 0 then [Term.zero.code, Term.one.code]
      else [(Term.var (t.2 - 1)).code]) :: s
  else if t.1 = 1 then [] :: s
  else if t.1 = 2 then [Term.one.code] :: s
  else if t.1 = 3 then binaryStack addCodes s
  else if t.1 = 4 then binaryStack mulCodes s
  else if t.1 = 5 then unaryStack negCodes s
  else []

def abstractRun (c : Code) (s : List PolyCode) : List PolyCode :=
  c.foldl (fun s t => abstractStep t s) s

def abstractCode (c : Code) : PolyCode := (abstractRun c []).getD 0 []

theorem primrec_abstractStep : Primrec₂ abstractStep := by
  have hvar : Primrec (fun z : Token × List PolyCode =>
      (if z.1.2 = 0 then [Term.zero.code, Term.one.code]
        else [(Term.var (z.1.2 - 1)).code]) :: z.2) :=
    Primrec.list_cons.comp
      (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0))
        (Primrec.const _) (Primrec.list_cons.comp
          (primrec_var_code (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)))
          (Primrec.const []))) Primrec.snd
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)) hvar
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1))
      (Primrec.list_cons.comp (Primrec.const []) Primrec.snd)
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 2))
        (Primrec.list_cons.comp (Primrec.const [Term.one.code]) Primrec.snd)
        (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 3))
          ((primrec_binaryStack primrec_addCodes).comp Primrec.snd)
          (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 4))
            ((primrec_binaryStack primrec_mulCodes).comp Primrec.snd)
            (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 5))
              ((primrec_unaryStack primrec_negCodes).comp Primrec.snd) (Primrec.const []))))))

theorem primrec_abstractRun : Primrec₂ abstractRun :=
  Primrec.list_foldl Primrec.fst Primrec.snd
    (primrec_abstractStep.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)).to₂

theorem primrec_abstractCode : Primrec abstractCode :=
  (Primrec.list_getD []).comp (primrec_abstractRun.comp Primrec.id (Primrec.const []))
    (Primrec.const 0)

theorem abstractRun_append (a b : Code) (s : List PolyCode) :
    abstractRun (a ++ b) s = abstractRun b (abstractRun a s) := List.foldl_append

theorem abstractRun_term_code (t : Term) (s : List PolyCode) :
    abstractRun t.code s = (abstract0 t).map Term.code :: s := by
  induction t generalizing s with
  | var n => cases n <;> simp [Term.code, abstractRun, abstractStep, abstract0]
  | zero => rfl
  | one => rfl
  | add a b ha hb =>
      rw [Term.code, abstractRun_append, abstractRun_append, ha, hb]
      change addCodes ((abstract0 a).map Term.code) ((abstract0 b).map Term.code) :: s = _
      rw [addCodes_map]
      rfl
  | mul a b ha hb =>
      rw [Term.code, abstractRun_append, abstractRun_append, ha, hb]
      change mulCodes ((abstract0 a).map Term.code) ((abstract0 b).map Term.code) :: s = _
      rw [mulCodes_map]
      rfl
  | neg a ha =>
      rw [Term.code, abstractRun_append, ha]
      change negCodes ((abstract0 a).map Term.code) :: s = _
      rw [negCodes_map]
      rfl

theorem abstractCode_term_code (t : Term) :
    abstractCode t.code = (abstract0 t).map Term.code := by
  rw [abstractCode, abstractRun_term_code]
  rfl

theorem primrec_abstract0_code {A : Type*} [Primcodable A]
    {t : A → Term} (ht : Primrec (fun a => (t a).code)) :
    Primrec (fun a => (abstract0 (t a)).map Term.code) :=
  (primrec_abstractCode.comp ht).of_eq (fun a => abstractCode_term_code (t a))

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

def leadingTableCode (p : PolyCode) (k : Code → Code) : Code :=
  sizeTableCode p ((List.range (p.length + 1)).map (fun n =>
    k (if n = 0 then Term.zero.code else p.getD (n - 1) Term.zero.code)))

theorem leadingTableCode_eq (p : TermPoly) (k : Term → Formula) (g : Code → Code)
    (hg : ∀ t, g t.code = (k t).code) :
    leadingTableCode (p.map Term.code) g = (leadingCases p k).code := by
  unfold leadingTableCode
  rw [List.length_map]
  have heq (n : ℕ) :
      g (if n = 0 then Term.zero.code else (p.map Term.code).getD (n - 1) Term.zero.code) =
        (k (if n = 0 then Term.zero else coefficient p (n - 1))).code := by
    by_cases hn : n = 0
    · simpa only [hn, ↓reduceIte] using hg Term.zero
    · simpa only [if_neg hn, coefficient_code] using hg (coefficient p (n - 1))
  simp_rw [heq]
  exact sizeTableCode_eq p (fun n => k (if n = 0 then Term.zero else coefficient p (n - 1)))

theorem primrec_leadingTableCode {A : Type*} [Primcodable A]
    {p : A → PolyCode} {k : A → Code → Code}
    (hp : Primrec p) (hk : Primrec (fun z : A × Code => k z.1 z.2)) :
    Primrec (fun a => leadingTableCode (p a) (k a)) := by
  have hlen := Primrec.nat_add.comp (Primrec.list_length.comp hp) (Primrec.const 1)
  have hcoeff : Primrec (fun z : A × ℕ => (p z.1).getD (z.2 - 1) Term.zero.code) :=
    (Primrec.list_getD _).comp (hp.comp Primrec.fst)
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))
  have hterm : Primrec (fun z : A × ℕ =>
      if z.2 = 0 then Term.zero.code else (p z.1).getD (z.2 - 1) Term.zero.code) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const _) hcoeff
  exact primrec_sizeTableCode.comp hp
    (Primrec.list_map (Primrec.list_range.comp hlen)
      (hk.comp (Primrec.fst.pair hterm)).to₂)

theorem primrec_leadingCases_code {A : Type*} [Primcodable A]
    {p : A → TermPoly} {k : A → Term → Formula} {g : A → Code → Code}
    (hp : Primrec (fun a => (p a).map Term.code))
    (hg : Primrec (fun z : A × Code => g z.1 z.2))
    (hkg : ∀ a t, g a t.code = (k a t).code) :
    Primrec (fun a => (leadingCases (p a) (k a)).code) :=
  (primrec_leadingTableCode hp hg).of_eq
    (fun a => leadingTableCode_eq (p a) (k a) (g a) (hkg a))

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

noncomputable def realSize (p : Polynomial ℝ) : ℕ := by
  classical
  exact if p = 0 then 0 else p.natDegree + 1

theorem realSize_eq_specializedSize (ρ : ℕ → ℝ) (p : TermPoly) :
    realSize (specialize ρ p) = specializedSize ρ p := rfl

theorem realSize_le_iff_degree_lt (p : Polynomial ℝ) (n : ℕ) :
    realSize p ≤ n ↔ p.degree < n := by
  classical
  by_cases hp : p = 0
  · simp [realSize, hp]
  · simp only [realSize, if_neg hp, Polynomial.degree_eq_natDegree hp,
      Nat.cast_lt, Nat.add_one_le_iff]

theorem realSize_eq_degree_succ (p : Polynomial ℝ) : realSize p = p.degree.succ := by
  classical
  by_cases hp : p = 0 <;>
    simp [realSize, hp, Polynomial.withBotSucc_degree_eq_natDegree_add_one]

theorem realSize_eq_zero_iff (p : Polynomial ℝ) : realSize p = 0 ↔ p = 0 := by
  classical
  simp [realSize]

theorem realSize_lt_of_degree_lt (p q : Polynomial ℝ) (h : p.degree < q.degree) :
    realSize p < realSize q := by
  simpa only [realSize_eq_degree_succ] using WithBot.succ_lt_succ h

noncomputable def realRemainderStep (r q : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C q.leadingCoeff * r -
    (Polynomial.C r.leadingCoeff * Polynomial.X ^ (r.natDegree - q.natDegree)) * q

theorem degree_realRemainderStep_lt (r q : Polynomial ℝ)
    (hr : r ≠ 0) (hq : q ≠ 0) (hqr : q.natDegree ≤ r.natDegree) :
    (realRemainderStep r q).degree < r.degree := by
  have hq' := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hr' := Polynomial.leadingCoeff_ne_zero.mpr hr
  have hdeg : (Polynomial.C q.leadingCoeff * r).degree = r.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hq', zero_add]
  rw [realRemainderStep, ← hdeg]
  apply Polynomial.degree_sub_lt_left
  case hd =>
    rw [hdeg, Polynomial.degree_mul, Polynomial.degree_C_mul_X_pow _ hr',
      Polynomial.degree_eq_natDegree hr, Polynomial.degree_eq_natDegree hq,
      ← Nat.cast_add, Nat.sub_add_cancel hqr]
  case hp0 => exact mul_ne_zero (Polynomial.C_ne_zero.mpr hq') hr
  case hlc => simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_X, one_pow, one_mul, mul_comm]

noncomputable def realReductionMonomial (r q : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C r.leadingCoeff * Polynomial.X ^ (realSize r - realSize q)

noncomputable def realPseudoLoop (q : Polynomial ℝ) :
    ℕ → ℕ → Polynomial ℝ → Polynomial ℝ → ℕ × Polynomial ℝ × Polynomial ℝ
  | 0, c, a, r => (c, a, r)
  | n + 1, c, a, r =>
      if realSize r < realSize q then (c, a, r) else
        let m := realReductionMonomial r q
        realPseudoLoop q n (c + 1) (Polynomial.C q.leadingCoeff * a + m)
          (Polynomial.C q.leadingCoeff * r - m * q)

theorem real_reduction_preserves_identity (p q a r m : Polynomial ℝ) (c : ℕ)
    (h : Polynomial.C (q.leadingCoeff ^ c) * p = a * q + r) :
    Polynomial.C (q.leadingCoeff ^ (c + 1)) * p =
      (Polynomial.C q.leadingCoeff * a + m) * q +
        (Polynomial.C q.leadingCoeff * r - m * q) := by
  have h' := congrArg (fun f : Polynomial ℝ => Polynomial.C q.leadingCoeff * f) h
  simp only [pow_succ, map_mul]
  convert h' using 1 <;> ring

theorem realPseudoLoop_identity (p q : Polynomial ℝ) (fuel c : ℕ)
    (a r : Polynomial ℝ)
    (h : Polynomial.C (q.leadingCoeff ^ c) * p = a * q + r) :
    let out := realPseudoLoop q fuel c a r
    Polynomial.C (q.leadingCoeff ^ out.1) * p = out.2.1 * q + out.2.2 := by
  induction fuel generalizing c a r with
  | zero => exact h
  | succ n ih =>
      simp only [realPseudoLoop]
      split_ifs with hs
      · exact h
      · exact ih (c + 1) _ _
          (real_reduction_preserves_identity p q a r (realReductionMonomial r q) c h)

theorem realReduction_size_lt (r q : Polynomial ℝ) (hq : q ≠ 0)
    (hqr : realSize q ≤ realSize r) :
    realSize (Polynomial.C q.leadingCoeff * r - realReductionMonomial r q * q) <
      realSize r := by
  have hr : r ≠ 0 := by
    intro hz
    have hs := (realSize_eq_zero_iff r).mpr hz
    have hq' := (realSize_eq_zero_iff q).not.mpr hq
    omega
  have hdeg : q.natDegree ≤ r.natDegree := by
    simpa only [realSize, if_neg hq, if_neg hr, Nat.add_le_add_iff_right] using hqr
  apply realSize_lt_of_degree_lt
  simpa only [realReductionMonomial, realSize, if_neg hr, if_neg hq,
    Nat.add_sub_add_right, realRemainderStep] using
      degree_realRemainderStep_lt r q hr hq hdeg

theorem realPseudoLoop_remainder_size_lt (q : Polynomial ℝ) (fuel c : ℕ)
    (a r : Polynomial ℝ) (hq : q ≠ 0) (hf : realSize r ≤ fuel) :
    realSize (realPseudoLoop q fuel c a r).2.2 < realSize q := by
  induction fuel generalizing c a r with
  | zero =>
      change realSize r < realSize q
      have hq' := (realSize_eq_zero_iff q).not.mpr hq
      omega
  | succ n ih =>
      simp only [realPseudoLoop]
      split_ifs with hs
      · exact hs
      · apply ih
        have hd := realReduction_size_lt r q hq (Nat.le_of_not_gt hs)
        omega

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

def shift (n : ℕ) (p : TermPoly) : TermPoly := List.replicate n Term.zero ++ p

def termMonomial (n : ℕ) (a : Term) : TermPoly := shift n [a]

theorem specialize_add (ρ : ℕ → ℝ) (p q : TermPoly) :
    specialize ρ (add p q) = specialize ρ p + specialize ρ q := by
  induction p generalizing q <;> cases q <;>
    simp_all [add, specialize, Term.eval]
  ring

theorem specialize_scale (ρ : ℕ → ℝ) (a : Term) (p : TermPoly) :
    specialize ρ (scale a p) = Polynomial.C (a.eval ρ) * specialize ρ p := by
  induction p <;> simp_all [scale, specialize, Term.eval]
  ring

theorem specialize_neg (ρ : ℕ → ℝ) (p : TermPoly) :
    specialize ρ (neg p) = -specialize ρ p := by
  induction p <;> simp_all [neg, specialize, Term.eval]
  ring

theorem specialize_mul (ρ : ℕ → ℝ) (p q : TermPoly) :
    specialize ρ (mul p q) = specialize ρ p * specialize ρ q := by
  induction p <;> simp_all [mul, specialize_add, specialize_scale, specialize, Term.eval]
  ring

theorem specialize_shift (ρ : ℕ → ℝ) (n : ℕ) (p : TermPoly) :
    specialize ρ (shift n p) = specialize ρ p * Polynomial.X ^ n := by
  induction n <;> simp_all [shift, List.replicate_succ, specialize, Term.eval, pow_succ]
  exact mul_assoc _ _ _

theorem specialize_termMonomial (ρ : ℕ → ℝ) (n : ℕ) (a : Term) :
    specialize ρ (termMonomial n a) = Polynomial.C (a.eval ρ) * Polynomial.X ^ n := by
  simp only [termMonomial, specialize_shift, specialize, zero_mul, add_zero]

theorem realSize_specialize_le_length (ρ : ℕ → ℝ) (p : TermPoly) :
    realSize (specialize ρ p) ≤ p.length :=
  (realSize_le_iff_degree_lt _ _).mpr
    ((Polynomial.degree_lt_iff_coeff_zero _ _).mpr (fun n hn => by
      simp only [coeff_specialize, coefficient, List.getElem?_eq_none hn,
        Option.getD_none, Term.eval]))

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

def pseudoDivLoopCases (q : TermPoly) (sq : ℕ) (cq : Term) :
    ℕ → ℕ → TermPoly → TermPoly → (ℕ → TermPoly → TermPoly → Formula) → Formula
  | 0, c, a, r, k => k c a r
  | n + 1, c, a, r, k =>
      sizeCases r (fun sr => if sr < sq then k c a r else
        leadingCases r (fun cr =>
          let m := termMonomial (sr - sq) cr
          pseudoDivLoopCases q sq cq n (c + 1)
            (add (scale cq a) m) (add (scale cq r) (neg (mul m q))) k))

def pseudoDivCases (p q : TermPoly)
    (k : ℕ → TermPoly → TermPoly → Formula) : Formula :=
  sizeCases q (fun sq => if sq = 0 then k 0 [] p else
    leadingCases q (fun cq => pseudoDivLoopCases q sq cq p.length 0 [] p k))

noncomputable def realPseudoDiv (p q : Polynomial ℝ) (fuel : ℕ) :
    ℕ × Polynomial ℝ × Polynomial ℝ :=
  if realSize q = 0 then (0, 0, p) else realPseudoLoop q fuel 0 0 p

theorem holds_pseudoDivLoopCases (q : TermPoly) (sq : ℕ) (cq : Term)
    (fuel c : ℕ) (a r : TermPoly) (k : ℕ → TermPoly → TermPoly → Formula)
    (ρ : ℕ → ℝ) (P : ℕ → Polynomial ℝ → Polynomial ℝ → Prop)
    (hsq : sq = realSize (specialize ρ q))
    (hcq : cq.eval ρ = (specialize ρ q).leadingCoeff)
    (hk : ∀ c a r, (k c a r).Holds ρ ↔ P c (specialize ρ a) (specialize ρ r)) :
    (pseudoDivLoopCases q sq cq fuel c a r k).Holds ρ ↔
      let out := realPseudoLoop (specialize ρ q) fuel c (specialize ρ a) (specialize ρ r)
      P out.1 out.2.1 out.2.2 := by
  subst sq
  induction fuel generalizing c a r with
  | zero => exact hk c a r
  | succ n ih =>
      rw [pseudoDivLoopCases, holds_sizeCases, ← realSize_eq_specializedSize]
      by_cases hs : realSize (specialize ρ r) < realSize (specialize ρ q)
      · simpa only [if_pos hs, realPseudoLoop] using hk c a r
      · rw [if_neg hs, leadingCases, holds_sizeCases, ih]
        simp only [realPseudoLoop, if_neg hs, specialize_add, specialize_scale,
          specialize_neg, specialize_mul, specialize_termMonomial,
          eval_leading_selected, hcq, realReductionMonomial, sub_eq_add_neg]

theorem holds_pseudoDivCases (p q : TermPoly)
    (k : ℕ → TermPoly → TermPoly → Formula) (ρ : ℕ → ℝ)
    (P : ℕ → Polynomial ℝ → Polynomial ℝ → Prop)
    (hk : ∀ c a r, (k c a r).Holds ρ ↔ P c (specialize ρ a) (specialize ρ r)) :
    (pseudoDivCases p q k).Holds ρ ↔
      let out := realPseudoDiv (specialize ρ p) (specialize ρ q) p.length
      P out.1 out.2.1 out.2.2 := by
  rw [pseudoDivCases, holds_sizeCases, ← realSize_eq_specializedSize]
  by_cases hq : realSize (specialize ρ q) = 0
  · simpa only [if_pos hq, realPseudoDiv, specialize] using hk 0 [] p
  · rw [if_neg hq, leadingCases, holds_sizeCases]
    simpa only [realPseudoDiv, if_neg hq, specialize] using
      (holds_pseudoDivLoopCases q (realSize (specialize ρ q))
        (if specializedSize ρ q = 0 then Term.zero else
          coefficient q (specializedSize ρ q - 1)) p.length 0 [] p k ρ P rfl
        (eval_leading_selected q ρ) hk)

theorem realPseudoDiv_spec (p q : Polynomial ℝ) (fuel : ℕ)
    (hf : realSize p ≤ fuel) :
    let out := realPseudoDiv p q fuel
    Polynomial.C (q.leadingCoeff ^ out.1) * p = out.2.1 * q + out.2.2 ∧
      (q = 0 ∨ out.2.2.degree < q.degree) := by
  by_cases hq : q = 0
  · simp [realPseudoDiv, realSize, hq]
  · have hs := (realSize_eq_zero_iff q).not.mpr hq
    rw [realPseudoDiv, if_neg hs]
    refine ⟨realPseudoLoop_identity p q fuel 0 0 p (by simp), Or.inr ?_⟩
    apply WithBot.succ_strictMono.lt_iff_lt.mp
    simpa only [realSize_eq_degree_succ] using
      realPseudoLoop_remainder_size_lt q fuel 0 0 p hq hf

theorem pseudoDivCases_certified (p q : TermPoly) (ρ : ℕ → ℝ) :
    let out := realPseudoDiv (specialize ρ p) (specialize ρ q) p.length
    Polynomial.C ((specialize ρ q).leadingCoeff ^ out.1) * specialize ρ p =
        out.2.1 * specialize ρ q + out.2.2 ∧
      (specialize ρ q = 0 ∨ out.2.2.degree < (specialize ρ q).degree) :=
  realPseudoDiv_spec _ _ _ (realSize_specialize_le_length ρ p)

theorem pseudoDivCases_correct (p q : TermPoly)
    (k : ℕ → TermPoly → TermPoly → Formula) (ρ : ℕ → ℝ)
    (P : ℕ → Polynomial ℝ → Polynomial ℝ → Prop)
    (hk : ∀ c a r, (k c a r).Holds ρ ↔ P c (specialize ρ a) (specialize ρ r)) :
    ∃ (c : ℕ) (a r : Polynomial ℝ),
      Polynomial.C ((specialize ρ q).leadingCoeff ^ c) * specialize ρ p =
          a * specialize ρ q + r ∧
        (specialize ρ q = 0 ∨ r.degree < (specialize ρ q).degree) ∧
        ((pseudoDivCases p q k).Holds ρ ↔ P c a r) :=
  ⟨_, _, _, (pseudoDivCases_certified p q ρ).1,
    (pseudoDivCases_certified p q ρ).2, holds_pseudoDivCases p q k ρ P hk⟩

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

theorem computable_of_decreasing_code_body (f fuel : ℕ → ℕ)
    (body : Nat.Partrec.Code → ℕ → Part ℕ) (hbody : Partrec₂ body)
    (hstep : ∀ c n,
      (∀ m, fuel m < fuel n → Nat.Partrec.Code.eval c m = Part.some (f m)) →
      body c n = Part.some (f n)) : Computable f := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point₂ hbody
  have htotal : ∀ n, Nat.Partrec.Code.eval c n = Part.some (f n) := by
    intro n
    induction n using (measure fuel).wf.induction with
    | h n ih =>
      exact (congrFun hc n).trans (hstep c n ih)
  exact (Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.id).of_eq_tot
    (fun n => by simp [htotal])

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003

def traversePart {α β : Type*} (f : α → Part β) : List α → Part (List β)
  | [] => Part.some []
  | x :: xs => (f x).bind fun y => (traversePart f xs).map (List.cons y)

theorem mem_traversePart_iff {α β : Type*} (f : α → Part β)
    (xs : List α) (ys : List β) :
    ys ∈ traversePart f xs ↔ List.Forall₂ (fun x y => y ∈ f x) xs ys := by
  induction xs generalizing ys with
  | nil =>
    simp only [traversePart, Part.mem_some_iff, List.forall₂_nil_left_iff]
  | cons x xs ih =>
    constructor
    · intro h
      rcases Part.mem_bind_iff.mp h with ⟨y, hy, ht⟩
      rcases (Part.mem_map_iff (List.cons y)).mp ht with ⟨zs, hzs, rfl⟩
      exact List.Forall₂.cons hy ((ih zs).mp hzs)
    · intro h
      cases h with
      | cons hy hz => exact Part.mem_bind hy (Part.mem_map _ ((ih _).mpr hz))

theorem traversePart_eq_some_of_mem {α β : Type*} (f : α → Part β)
    (g : α → β) (xs : List α) (h : ∀ x ∈ xs, g x ∈ f x) :
    traversePart f xs = Part.some (xs.map g) := by
  apply Part.eq_some_iff.mpr
  rw [mem_traversePart_iff, List.forall₂_map_right_iff, List.forall₂_same]
  exact h

theorem traversePart_eq_some_map {α β : Type*} (f : α → Part β)
    (g : α → β) (xs : List α) (h : ∀ x ∈ xs, f x = Part.some (g x)) :
    traversePart f xs = Part.some (xs.map g) :=
  traversePart_eq_some_of_mem f g xs (fun x hx => Part.eq_some_iff.mp (h x hx))

theorem traversePart_some {α β : Type*} (g : α → β) (xs : List α) :
    traversePart (fun x => Part.some (g x)) xs = Part.some (xs.map g) :=
  traversePart_eq_some_map _ g xs (fun _ _ => rfl)

theorem traversePart_map_eq_some {γ α β : Type*} (f : α → Part β)
    (input : γ → α) (output : γ → β) (xs : List γ)
    (h : ∀ x ∈ xs, output x ∈ f (input x)) :
    traversePart f (xs.map input) = Part.some (xs.map output) := by
  apply Part.eq_some_iff.mpr
  rw [mem_traversePart_iff, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff, List.forall₂_same]
  exact h

private def traversePartStep {A α β : Type*} (f : A → α → Part β)
    (s : A × List α × List β) : Part (List β ⊕ (A × List α × List β)) :=
  s.2.1.head?.casesOn (Part.some (Sum.inl s.2.2.reverse))
    (fun x => (f s.1 x).map fun y => Sum.inr (s.1, s.2.1.tail, y :: s.2.2))

set_option backward.isDefEq.respectTransparency false in
private theorem traversePartStep_fix_nil {A α β : Type*} (f : A → α → Part β)
    (a : A) (acc : List β) :
    PFun.fix (traversePartStep f) (a, [], acc) = Part.some acc.reverse := by
  apply Part.ext
  intro ys
  rw [PFun.mem_fix_iff]
  simp [traversePartStep]

set_option backward.isDefEq.respectTransparency false in
private theorem traversePartStep_fix_cons {A α β : Type*} (f : A → α → Part β)
    (a : A) (x : α) (xs : List α) (acc : List β) :
    PFun.fix (traversePartStep f) (a, x :: xs, acc) =
      (f a x).bind (fun y => PFun.fix (traversePartStep f) (a, xs, y :: acc)) := by
  apply Part.ext
  intro ys
  rw [PFun.mem_fix_iff]
  simp [traversePartStep, Part.mem_map_iff, Part.mem_bind_iff]

private theorem traversePartStep_fix_eq {A α β : Type*} (f : A → α → Part β)
    (a : A) (xs : List α) (acc : List β) :
    PFun.fix (traversePartStep f) (a, xs, acc) =
      (traversePart (f a) xs).map (fun ys => acc.reverse ++ ys) := by
  induction xs generalizing acc with
  | nil => simp only [traversePartStep_fix_nil, traversePart, Part.map_some, List.append_nil]
  | cons x xs ih =>
    simp only [traversePartStep_fix_cons, ih, traversePart, Part.map_bind,
      Part.map_map, List.reverse_cons, List.append_assoc, List.singleton_append,
      Function.comp_def]

theorem partrec_traversePart {A α β : Type*}
    [Primcodable A] [Primcodable α] [Primcodable β]
    {f : A → α → Part β} (hf : Partrec₂ f) :
    Partrec₂ (fun a xs => traversePart (f a) xs) := by
  have hStep : Partrec (traversePartStep f) := by
    apply Partrec.optionCasesOn_right
      (Primrec.list_head?.to_comp.comp (Computable.fst.comp Computable.snd))
      (Computable.sumInl.comp
        (Computable.list_reverse.comp (Computable.snd.comp Computable.snd)))
    apply Partrec.map (hf.comp (Computable.fst.comp Computable.fst) Computable.snd)
    have hState : Computable
        (fun p : ((A × List α × List β) × α) × β => p.1.1) :=
      Computable.fst.comp Computable.fst
    exact (Computable.sumInr.comp
      ((Computable.fst.comp hState).pair
        ((Primrec.list_tail.to_comp.comp (Computable.fst.comp (Computable.snd.comp hState))).pair
          (Computable.list_cons.comp Computable.snd
            (Computable.snd.comp (Computable.snd.comp hState)))))).to₂
  have hInit : Computable
      (fun p : A × List α => (p.1, p.2, ([] : List β))) :=
    Computable.fst.pair (Computable.snd.pair (Computable.const []))
  exact ((Partrec.fix hStep).comp hInit).of_eq (fun p => by
    simp only [traversePartStep_fix_eq, List.reverse_nil, List.nil_append]
    rfl)

end Grunbaum2003

namespace Grunbaum2003.FormulaCompiler.Parametric

def shiftCodes (n : ℕ) (p : PolyCode) : PolyCode :=
  List.replicate n Term.zero.code ++ p

def termMonomialCodes (n : ℕ) (a : Code) : PolyCode := shiftCodes n [a]

theorem shiftCodes_map (n : ℕ) (p : TermPoly) :
    shiftCodes n (p.map Term.code) = (shift n p).map Term.code := by
  simp only [shiftCodes, shift, List.map_append, List.map_replicate]

theorem termMonomialCodes_map (n : ℕ) (a : Term) :
    termMonomialCodes n a.code = (termMonomial n a).map Term.code :=
  shiftCodes_map n [a]

private theorem primrec_zeroCodes :
    Primrec (fun n : ℕ ↦ List.replicate n Term.zero.code) := by
  have h : Primrec (fun n : ℕ ↦ (List.range n).map (fun _ ↦ Term.zero.code)) :=
    Primrec.list_map Primrec.list_range (Primrec.const _).to₂
  exact h.of_eq (fun n ↦ by simp only [List.map_const', List.length_range])

theorem primrec_shiftCodes : Primrec₂ shiftCodes :=
  Primrec.list_append.comp (primrec_zeroCodes.comp Primrec.fst) Primrec.snd

theorem primrec_termMonomialCodes : Primrec₂ termMonomialCodes :=
  primrec_shiftCodes.comp Primrec.fst
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))

def quotientUpdateCodes (sq sr : ℕ) (cq cr : Code) (a : PolyCode) : PolyCode :=
  addCodes (scaleCodes cq a) (termMonomialCodes (sr - sq) cr)

def remainderUpdateCodes (sq sr : ℕ) (cq cr : Code) (r q : PolyCode) : PolyCode :=
  addCodes (scaleCodes cq r) (negCodes (mulCodes (termMonomialCodes (sr - sq) cr) q))

theorem quotientUpdateCodes_map (sq sr : ℕ) (cq cr : Term) (a : TermPoly) :
    quotientUpdateCodes sq sr cq.code cr.code (a.map Term.code) =
      (add (scale cq a) (termMonomial (sr - sq) cr)).map Term.code := by
  unfold quotientUpdateCodes
  rw [scaleCodes_map, termMonomialCodes_map, addCodes_map]

theorem remainderUpdateCodes_map (sq sr : ℕ) (cq cr : Term) (r q : TermPoly) :
    remainderUpdateCodes sq sr cq.code cr.code (r.map Term.code) (q.map Term.code) =
      (add (scale cq r) (neg (mul (termMonomial (sr - sq) cr) q))).map Term.code := by
  unfold remainderUpdateCodes
  rw [scaleCodes_map, termMonomialCodes_map, mulCodes_map, negCodes_map, addCodes_map]

theorem primrec_quotientUpdateCodes {A : Type*} [Primcodable A]
    {sq sr : A → ℕ} {cq cr : A → Code} {a : A → PolyCode}
    (hsq : Primrec sq) (hsr : Primrec sr) (hcq : Primrec cq) (hcr : Primrec cr)
    (ha : Primrec a) :
    Primrec (fun x ↦ quotientUpdateCodes (sq x) (sr x) (cq x) (cr x) (a x)) :=
  primrec_addCodes.comp (primrec_scaleCodes.comp hcq ha)
    (primrec_termMonomialCodes.comp (Primrec.nat_sub.comp hsr hsq) hcr)

theorem primrec_remainderUpdateCodes {A : Type*} [Primcodable A]
    {sq sr : A → ℕ} {cq cr : A → Code} {r q : A → PolyCode}
    (hsq : Primrec sq) (hsr : Primrec sr) (hcq : Primrec cq) (hcr : Primrec cr)
    (hr : Primrec r) (hq : Primrec q) :
    Primrec (fun x ↦ remainderUpdateCodes (sq x) (sr x) (cq x) (cr x) (r x) (q x)) :=
  primrec_addCodes.comp (primrec_scaleCodes.comp hcq hr)
    (primrec_negCodes.comp
      (primrec_mulCodes.comp
        (primrec_termMonomialCodes.comp (Primrec.nat_sub.comp hsr hsq) hcr) hq))

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

def evalCodeAt {S : Type*} [Primcodable S] (c : Nat.Partrec.Code) (s : S) : Part Code :=
  (Nat.Partrec.Code.eval c (Encodable.encode s)).map
    (fun n ↦ (Encodable.decode (α := Code) n).getD [])

theorem partrec_evalCodeAt {S : Type*} [Primcodable S] :
    Partrec₂ (@evalCodeAt S _) := by
  have heval : Partrec (fun z : Nat.Partrec.Code × S ↦
      Nat.Partrec.Code.eval z.1 (Encodable.encode z.2)) :=
    Nat.Partrec.Code.eval_part.comp Computable.fst (Computable.encode.comp Computable.snd)
  have hdec : Computable₂ (fun (_ : Nat.Partrec.Code × S) (n : ℕ) ↦
      (Encodable.decode (α := Code) n).getD []) :=
    ((Primrec.option_getD.comp Primrec.decode (Primrec.const [])).to_comp.comp
      Computable.snd).to₂
  exact (Partrec.map heval hdec).to₂

theorem evalCodeAt_eq_some {S : Type*} [Primcodable S]
    (c : Nat.Partrec.Code) (s : S) (out : Code)
    (h : Nat.Partrec.Code.eval c (Encodable.encode s) = Part.some (Encodable.encode out)) :
    evalCodeAt c s = Part.some out := by
  simp only [evalCodeAt, h, Part.map_some, Encodable.encodek, Option.getD_some]

def encodedTarget {S : Type*} [Primcodable S] (F : S → Code) (n : ℕ) : ℕ :=
  (Encodable.decode (α := S) n).casesOn 0 (fun s ↦ Encodable.encode (F s))

def encodedFuel {S : Type*} [Primcodable S] (fuel : S → ℕ) (n : ℕ) : ℕ :=
  (Encodable.decode (α := S) n).casesOn 0 fuel

def encodedStepBody {S : Type*} [Primcodable S]
    (stepBody : (S → Part Code) → S → Part Code)
    (c : Nat.Partrec.Code) (n : ℕ) : Part ℕ :=
  (Encodable.decode (α := S) n).casesOn (Part.some 0)
    (fun s ↦ (stepBody (evalCodeAt c) s).map Encodable.encode)

theorem computable_of_decreasing_step {S : Type*} [Primcodable S]
    (F : S → Code) (fuel : S → ℕ)
    (stepBody : (S → Part Code) → S → Part Code)
    (hbody : Partrec₂ (fun c (s : S) ↦ stepBody (evalCodeAt c) s))
    (hstep : ∀ (recCall : S → Part Code) (s : S),
      (∀ s', fuel s' < fuel s → recCall s' = Part.some (F s')) →
      stepBody recCall s = Part.some (F s)) :
    Computable F := by
  have hEncBody : Partrec₂ (encodedStepBody stepBody) := by
    change Partrec (fun p : Nat.Partrec.Code × ℕ ↦ encodedStepBody stepBody p.1 p.2)
    have ho : Computable (fun p : Nat.Partrec.Code × ℕ ↦ Encodable.decode (α := S) p.2) :=
      (Computable.decode (α := S)).comp Computable.snd
    have hf : Computable (fun _ : Nat.Partrec.Code × ℕ ↦ (0 : ℕ)) :=
      Computable.const 0
    have hcall : Partrec (fun z : (Nat.Partrec.Code × ℕ) × S ↦
        stepBody (evalCodeAt z.1.1) z.2) :=
      hbody.comp (Computable.fst.comp Computable.fst) Computable.snd
    have henc : Computable₂ (fun (_ : (Nat.Partrec.Code × ℕ) × S) (out : Code) ↦
        Encodable.encode out) :=
      (Computable.encode.comp Computable.snd).to₂
    exact Partrec.optionCasesOn_right ho hf (Partrec.map hcall henc).to₂
  have hEncStep : ∀ c n,
      (∀ m, encodedFuel fuel m < encodedFuel fuel n →
        Nat.Partrec.Code.eval c m = Part.some (encodedTarget F m)) →
      encodedStepBody stepBody c n = Part.some (encodedTarget F n) := by
    intro c n ih
    cases hdec : Encodable.decode (α := S) n with
    | none => simp only [encodedStepBody, encodedTarget, hdec]
    | some s =>
      simp only [encodedStepBody, encodedTarget, hdec]
      have hrec : ∀ s', fuel s' < fuel s → evalCodeAt c s' = Part.some (F s') := by
        intro s' hlt
        have hlt' : encodedFuel fuel (Encodable.encode s') < encodedFuel fuel n := by
          simpa only [encodedFuel, Encodable.encodek, hdec] using hlt
        have heval := ih (Encodable.encode s') hlt'
        rw [encodedTarget, Encodable.encodek] at heval
        exact evalCodeAt_eq_some c s' (F s') heval
      rw [hstep (evalCodeAt c) s hrec, Part.map_some]
  have hCompNat : Computable (encodedTarget F) :=
    computable_of_decreasing_code_body (encodedTarget F) (encodedFuel fuel)
      (encodedStepBody stepBody) hEncBody hEncStep
  have hDecode : Computable (fun n : ℕ ↦ (Encodable.decode (α := Code) n).getD []) :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const [])).to_comp
  exact ((hDecode.comp hCompNat).comp Computable.encode).of_eq (fun s ↦ by
    simp only [encodedTarget, Encodable.encodek, Option.getD_some])

theorem partrec_ite_some {α σ : Type*} [Primcodable α] [Primcodable σ]
    {P : α → Prop} [DecidablePred P] {f : α → σ} {g : α → Part σ}
    (hP : Computable (fun a ↦ decide (P a)))
    (hf : Computable f) (hg : Partrec g) :
    Partrec (fun a ↦ if P a then Part.some (f a) else g a) := by
  have hb : Computable (fun a ↦ cond (decide (P a)) 0 1) :=
    Computable.cond hP (Computable.const 0) (Computable.const 1)
  refine (Partrec.nat_casesOn_right hb hf (hg.comp Computable.fst).to₂).of_eq (fun a ↦ ?_)
  by_cases h : P a <;> simp [h]

theorem computable_list_map {A α β : Type*}
    [Primcodable A] [Primcodable α] [Primcodable β]
    {l : A → List α} {f : A → α → β}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable (fun a ↦ (l a).map (f a)) :=
  ((partrec_traversePart hf.partrec₂).comp Computable.id hl).of_eq
    (fun a ↦ traversePart_some (f a) (l a))

def leadingCoeffCode (p : PolyCode) (j : ℕ) : Code :=
  if j = 0 then Term.zero.code else p.getD (j - 1) Term.zero.code

theorem primrec_leadingCoeffCode : Primrec₂ leadingCoeffCode :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.const Term.zero.code)
    ((Primrec.list_getD Term.zero.code).comp Primrec.fst
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))

theorem computable_sizeTableCode_range {A : Type*} [Primcodable A]
    {p : A → PolyCode} {k : A → ℕ → Code}
    (hp : Computable p) (hk : Computable (fun z : A × ℕ ↦ k z.1 z.2)) :
    Computable (fun a ↦ sizeTableCode (p a)
      ((List.range ((p a).length + 1)).map (fun i ↦ k a i))) := by
  have hlen : Computable (fun a ↦ (p a).length + 1) :=
    (Primrec.nat_add.comp Primrec.list_length (Primrec.const 1)).to_comp.comp hp
  have hrange : Computable (fun a ↦ List.range ((p a).length + 1)) :=
    Primrec.list_range.to_comp.comp hlen
  exact (primrec_sizeTableCode.to_comp.comp hp (computable_list_map hrange hk.to₂)).of_eq
    (fun _ ↦ rfl)

theorem computable_leadingTableCode {A : Type*} [Primcodable A]
    {p : A → PolyCode} {k : A → Code → Code}
    (hp : Computable p) (hk : Computable (fun z : A × Code ↦ k z.1 z.2)) :
    Computable (fun a ↦ leadingTableCode (p a) (k a)) := by
  have hterm : Computable (fun z : A × ℕ ↦ leadingCoeffCode (p z.1) z.2) :=
    primrec_leadingCoeffCode.to_comp.comp (hp.comp Computable.fst) Computable.snd
  have hk' : Computable (fun z : A × ℕ ↦ k z.1 (leadingCoeffCode (p z.1) z.2)) :=
    (hk.comp (Computable.fst.pair hterm)).of_eq (fun _ ↦ rfl)
  exact (computable_sizeTableCode_range (p := p)
    (k := fun a j ↦ k a (leadingCoeffCode (p a) j)) hp hk').of_eq (fun _ ↦ rfl)

def pseudoDivLoopCode (q : PolyCode) (sq : ℕ) (cq : Code) :
    ℕ → ℕ → PolyCode → PolyCode → (ℕ → PolyCode → PolyCode → Code) → Code
  | 0, c, a, r, k => k c a r
  | n + 1, c, a, r, k =>
      sizeTableCode r ((List.range (r.length + 1)).map (fun sr ↦
        if sr < sq then k c a r else
          leadingTableCode r (fun cr ↦
            pseudoDivLoopCode q sq cq n (c + 1)
              (quotientUpdateCodes sq sr cq cr a)
              (remainderUpdateCodes sq sr cq cr r q) k)))

def pseudoDivCode (p q : PolyCode)
    (k : ℕ → PolyCode → PolyCode → Code) : Code :=
  sizeTableCode q ((List.range (q.length + 1)).map (fun sq ↦
    if sq = 0 then k 0 [] p else
      leadingTableCode q (fun cq ↦
        pseudoDivLoopCode q sq cq p.length 0 [] p k)))

theorem pseudoDivLoopCode_eq (q : TermPoly) (sq : ℕ) (cq : Term)
    (fuel c : ℕ) (a r : TermPoly)
    (k : ℕ → TermPoly → TermPoly → Formula)
    (kCode : ℕ → PolyCode → PolyCode → Code)
    (hk : ∀ c a r, kCode c (a.map Term.code) (r.map Term.code) = (k c a r).code) :
    pseudoDivLoopCode (q.map Term.code) sq cq.code fuel c
      (a.map Term.code) (r.map Term.code) kCode =
      (pseudoDivLoopCases q sq cq fuel c a r k).code := by
  induction fuel generalizing c a r with
  | zero => exact hk c a r
  | succ n ih =>
    unfold pseudoDivLoopCode pseudoDivLoopCases
    rw [List.length_map]
    have hbranch (sr : ℕ) :
        (if sr < sq then kCode c (a.map Term.code) (r.map Term.code) else
          leadingTableCode (r.map Term.code) (fun cr ↦
            pseudoDivLoopCode (q.map Term.code) sq cq.code n (c + 1)
              (quotientUpdateCodes sq sr cq.code cr (a.map Term.code))
              (remainderUpdateCodes sq sr cq.code cr (r.map Term.code) (q.map Term.code))
              kCode)) =
        (if sr < sq then k c a r else
          leadingCases r (fun cr ↦
            let m := termMonomial (sr - sq) cr
            pseudoDivLoopCases q sq cq n (c + 1)
              (add (scale cq a) m) (add (scale cq r) (neg (mul m q))) k)).code := by
      by_cases hs : sr < sq
      · simp only [if_pos hs, hk]
      · simp only [if_neg hs]
        refine leadingTableCode_eq r _ _ (fun cr ↦ ?_)
        rw [quotientUpdateCodes_map, remainderUpdateCodes_map]
        exact ih (c + 1) _ _
    simp_rw [hbranch]
    exact sizeTableCode_eq r _

theorem pseudoDivCode_eq (p q : TermPoly)
    (k : ℕ → TermPoly → TermPoly → Formula)
    (kCode : ℕ → PolyCode → PolyCode → Code)
    (hk : ∀ c a r, kCode c (a.map Term.code) (r.map Term.code) = (k c a r).code) :
    pseudoDivCode (p.map Term.code) (q.map Term.code) kCode =
      (pseudoDivCases p q k).code := by
  unfold pseudoDivCode pseudoDivCases
  rw [List.length_map, List.length_map]
  have hbranch (sq : ℕ) :
      (if sq = 0 then kCode 0 [] (p.map Term.code) else
        leadingTableCode (q.map Term.code) (fun cq ↦
          pseudoDivLoopCode (q.map Term.code) sq cq p.length 0 [] (p.map Term.code) kCode)) =
      (if sq = 0 then k 0 [] p else
        leadingCases q (fun cq ↦ pseudoDivLoopCases q sq cq p.length 0 [] p k)).code := by
    by_cases hsq : sq = 0
    · simpa only [if_pos hsq, List.map_nil] using hk 0 [] p
    · simp only [if_neg hsq]
      refine leadingTableCode_eq q _ _ (fun cq ↦ ?_)
      exact pseudoDivLoopCode_eq q sq cq p.length 0 [] p k kCode hk
  simp_rw [hbranch]
  exact sizeTableCode_eq q _

theorem codeHolds_pseudoDivCode (p q : TermPoly)
    (k : ℕ → TermPoly → TermPoly → Formula)
    (kCode : ℕ → PolyCode → PolyCode → Code)
    (hk : ∀ c a r, kCode c (a.map Term.code) (r.map Term.code) = (k c a r).code)
    (ρ : ℕ → ℝ) (P : ℕ → Polynomial ℝ → Polynomial ℝ → Prop)
    (hP : ∀ c a r, (k c a r).Holds ρ ↔ P c (specialize ρ a) (specialize ρ r)) :
    CodeHolds (pseudoDivCode (p.map Term.code) (q.map Term.code) kCode) ρ ↔
      let out := realPseudoDiv (specialize ρ p) (specialize ρ q) p.length
      P out.1 out.2.1 out.2.2 := by
  rw [pseudoDivCode_eq p q k kCode hk, codeHolds_code]
  exact holds_pseudoDivCases p q k ρ P hP

theorem pseudoDivCode_correct (p q : TermPoly)
    (k : ℕ → TermPoly → TermPoly → Formula)
    (kCode : ℕ → PolyCode → PolyCode → Code)
    (hk : ∀ c a r, kCode c (a.map Term.code) (r.map Term.code) = (k c a r).code)
    (ρ : ℕ → ℝ) (P : ℕ → Polynomial ℝ → Polynomial ℝ → Prop)
    (hP : ∀ c a r, (k c a r).Holds ρ ↔ P c (specialize ρ a) (specialize ρ r)) :
    ∃ (c : ℕ) (a r : Polynomial ℝ),
      Polynomial.C ((specialize ρ q).leadingCoeff ^ c) * specialize ρ p =
          a * specialize ρ q + r ∧
        (specialize ρ q = 0 ∨ r.degree < (specialize ρ q).degree) ∧
        (CodeHolds (pseudoDivCode (p.map Term.code) (q.map Term.code) kCode) ρ ↔ P c a r) := by
  rw [pseudoDivCode_eq p q k kCode hk, codeHolds_code]
  exact pseudoDivCases_correct p q k ρ P hP

abbrev LoopFixed := PolyCode × ℕ × Code

abbrev LoopVars := ℕ × ℕ × PolyCode × PolyCode

abbrev LoopState (A : Type*) := A × LoopFixed × LoopVars

def loopFuel {A : Type*} (s : LoopState A) : ℕ := s.2.2.1

def evalLoopState {A : Type*} (kCode : A → ℕ → PolyCode → PolyCode → Code)
    (s : LoopState A) : Code :=
  pseudoDivLoopCode s.2.1.1 s.2.1.2.1 s.2.1.2.2
    s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2 (kCode s.1)

def nextLoopVars (fx : LoopFixed) (vr : LoopVars) (sr j : ℕ) : LoopVars :=
  let cr := leadingCoeffCode vr.2.2.2 j
  (vr.1 - 1, vr.2.1 + 1,
    quotientUpdateCodes fx.2.1 sr fx.2.2 cr vr.2.2.1,
    remainderUpdateCodes fx.2.1 sr fx.2.2 cr vr.2.2.2 fx.1)

def nextLoopState {A : Type*} (s : LoopState A) (sr j : ℕ) : LoopState A :=
  (s.1, s.2.1, nextLoopVars s.2.1 s.2.2 sr j)

theorem loopFuel_nextLoopState_lt {A : Type*} (s : LoopState A) (sr j : ℕ)
    (h : loopFuel s ≠ 0) :
    loopFuel (nextLoopState s sr j) < loopFuel s :=
  Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.one_pos

theorem primrec_nextLoopVars :
    Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦
      nextLoopVars z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  have hfx : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hvr : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hsr : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hj : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.2) := Primrec.snd
  have hq : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.1.1.1.1) :=
    Primrec.fst.comp hfx
  have hsq : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.1.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hfx)
  have hcq : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.1.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp hfx)
  have hfuel : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.1.1.2.1 - 1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp hvr) (Primrec.const 1)
  have hcount : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.1.1.2.2.1 + 1) :=
    Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp hvr)) (Primrec.const 1)
  have hquot : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.1.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hvr))
  have hrem : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦ z.1.1.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hvr))
  have hcr : Primrec (fun z : ((LoopFixed × LoopVars) × ℕ) × ℕ ↦
      leadingCoeffCode z.1.1.2.2.2.2 z.2) :=
    (primrec_leadingCoeffCode.comp hrem hj).of_eq (fun _ ↦ rfl)
  have hquot' := primrec_quotientUpdateCodes hsq hsr hcq hcr hquot
  have hrem' := primrec_remainderUpdateCodes hsq hsr hcq hcr hrem hq
  exact (hfuel.pair (hcount.pair (hquot'.pair hrem'))).of_eq (fun _ ↦ rfl)

theorem primrec_nextLoopState {A : Type*} [Primcodable A] :
    Primrec (fun z : (LoopState A × ℕ) × ℕ ↦ nextLoopState z.1.1 z.1.2 z.2) := by
  have hctx : Primrec (fun z : (LoopState A × ℕ) × ℕ ↦ z.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hfx : Primrec (fun z : (LoopState A × ℕ) × ℕ ↦ z.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hsub : Primrec (fun z : (LoopState A × ℕ) × ℕ ↦
      ((z.1.1.2, z.1.2), z.2)) :=
    ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd
  exact (hctx.pair (hfx.pair (primrec_nextLoopVars.comp hsub))).of_eq (fun _ ↦ rfl)

def loopInnerElse {A : Type*} (recCall : LoopState A → Part Code)
    (s : LoopState A) (sr : ℕ) : Part Code :=
  (traversePart (fun j ↦ recCall (nextLoopState s sr j))
    (List.range (s.2.2.2.2.2.length + 1))).map (sizeTableCode s.2.2.2.2.2)

def loopInnerStep {A : Type*} (kCode : A → ℕ → PolyCode → PolyCode → Code)
    (recCall : LoopState A → Part Code) (s : LoopState A) (sr : ℕ) : Part Code :=
  if sr < s.2.1.2.1 then
    Part.some (kCode s.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2)
  else
    loopInnerElse recCall s sr

def loopStepBody {A : Type*} (kCode : A → ℕ → PolyCode → PolyCode → Code)
    (recCall : LoopState A → Part Code) (s : LoopState A) : Part Code :=
  if s.2.2.1 = 0 then
    Part.some (kCode s.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2)
  else
    (traversePart (loopInnerStep kCode recCall s)
      (List.range (s.2.2.2.2.2.length + 1))).map (sizeTableCode s.2.2.2.2.2)

private theorem primrec_stateRem {A : Type*} [Primcodable A] :
    Primrec (fun s : LoopState A ↦ s.2.2.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem primrec_stateKArgs {A : Type*} [Primcodable A] :
    Primrec (fun s : LoopState A ↦ (s.1, s.2.2.2)) :=
  Primrec.fst.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem partrec_loopInnerCall {A : Type*} [Primcodable A] :
    Partrec₂ (fun (z : (Nat.Partrec.Code × LoopState A) × ℕ) (j : ℕ) ↦
      evalCodeAt z.1.1 (nextLoopState z.1.2 z.2 j)) := by
  have hs : Primrec (fun z : (Nat.Partrec.Code × LoopState A) × ℕ ↦ z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hc : Computable (fun w : ((Nat.Partrec.Code × LoopState A) × ℕ) × ℕ ↦ w.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hnext : Computable (fun w : ((Nat.Partrec.Code × LoopState A) × ℕ) × ℕ ↦
      nextLoopState w.1.1.2 w.1.2 w.2) :=
    (primrec_nextLoopState.comp
      (((hs.comp Primrec.fst).pair (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to_comp
  exact ((partrec_evalCodeAt (S := LoopState A)).comp hc hnext).to₂

private theorem partrec_loopInnerElse {A : Type*} [Primcodable A] :
    Partrec (fun z : (Nat.Partrec.Code × LoopState A) × ℕ ↦
      loopInnerElse (evalCodeAt z.1.1) z.1.2 z.2) := by
  have hrem : Primrec (fun z : (Nat.Partrec.Code × LoopState A) × ℕ ↦ z.1.2.2.2.2.2.2) :=
    primrec_stateRem.comp (Primrec.snd.comp Primrec.fst)
  have hrange : Computable (fun z : (Nat.Partrec.Code × LoopState A) × ℕ ↦
      List.range (z.1.2.2.2.2.2.2.length + 1)) :=
    (Primrec.list_range.comp
      (Primrec.nat_add.comp (Primrec.list_length.comp hrem) (Primrec.const 1))).to_comp
  have htrav : Partrec (fun z : (Nat.Partrec.Code × LoopState A) × ℕ ↦
      traversePart (fun j ↦ evalCodeAt z.1.1 (nextLoopState z.1.2 z.2 j))
        (List.range (z.1.2.2.2.2.2.2.length + 1))) :=
    (partrec_traversePart partrec_loopInnerCall).comp Computable.id hrange
  have hsize : Computable₂ (fun (z : (Nat.Partrec.Code × LoopState A) × ℕ) (tbl : PolyCode) ↦
      sizeTableCode z.1.2.2.2.2.2.2 tbl) := by
    have h1 : Primrec (fun p : ((Nat.Partrec.Code × LoopState A) × ℕ) × PolyCode ↦
        p.1.1.2.2.2.2.2.2) := hrem.comp Primrec.fst
    exact (primrec_sizeTableCode.comp h1 Primrec.snd).to_comp.to₂
  exact Partrec.map htrav hsize

private theorem primrec_loopInnerCond {A : Type*} [Primcodable A] :
    Primrec (fun z : (Nat.Partrec.Code × LoopState A) × ℕ ↦ decide (z.2 < z.1.2.2.1.2.1)) := by
  have hsq : Primrec (fun z : (Nat.Partrec.Code × LoopState A) × ℕ ↦ z.1.2.2.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))))
  exact (Primrec.nat_lt.comp Primrec.snd hsq).decide

private theorem computable_stateK {A : Type*} [Primcodable A]
    {kCode : A → ℕ → PolyCode → PolyCode → Code}
    (hkCode : Computable (fun z : A × ℕ × PolyCode × PolyCode ↦ kCode z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Computable (fun s : LoopState A ↦ kCode s.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2) :=
  hkCode.comp primrec_stateKArgs.to_comp

private theorem computable_loopInnerThen {A : Type*} [Primcodable A]
    {kCode : A → ℕ → PolyCode → PolyCode → Code}
    (hkCode : Computable (fun z : A × ℕ × PolyCode × PolyCode ↦ kCode z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Computable (fun z : (Nat.Partrec.Code × LoopState A) × ℕ ↦
      kCode z.1.2.1 z.1.2.2.2.2.1 z.1.2.2.2.2.2.1 z.1.2.2.2.2.2.2) :=
  ((computable_stateK hkCode).comp Computable.snd).comp Computable.fst

theorem partrec_loopInnerStep {A : Type*} [Primcodable A]
    {kCode : A → ℕ → PolyCode → PolyCode → Code}
    (hkCode : Computable (fun z : A × ℕ × PolyCode × PolyCode ↦ kCode z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Partrec₂ (fun (cs : Nat.Partrec.Code × LoopState A) (sr : ℕ) ↦
      loopInnerStep kCode (evalCodeAt cs.1) cs.2 sr) :=
  partrec_ite_some (P := fun z : (Nat.Partrec.Code × LoopState A) × ℕ ↦ z.2 < z.1.2.2.1.2.1)
    primrec_loopInnerCond.to_comp (computable_loopInnerThen hkCode) partrec_loopInnerElse

theorem partrec_loopStepBody {A : Type*} [Primcodable A]
    {kCode : A → ℕ → PolyCode → PolyCode → Code}
    (hkCode : Computable (fun z : A × ℕ × PolyCode × PolyCode ↦ kCode z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Partrec₂ (fun (c : Nat.Partrec.Code) (s : LoopState A) ↦
      loopStepBody kCode (evalCodeAt c) s) := by
  let CS := Nat.Partrec.Code × LoopState A
  change Partrec (fun cs : CS ↦ loopStepBody kCode (evalCodeAt cs.1) cs.2)
  have hs : Primrec (fun cs : CS ↦ cs.2) := Primrec.snd
  have hfuel : Primrec (fun cs : CS ↦ cs.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have hcond : Computable (fun cs : CS ↦ decide (cs.2.2.2.1 = 0)) :=
    (Primrec.eq.comp hfuel (Primrec.const 0)).decide.to_comp
  have hthen : Computable (fun cs : CS ↦
      kCode cs.2.1 cs.2.2.2.2.1 cs.2.2.2.2.2.1 cs.2.2.2.2.2.2) :=
    hkCode.comp (primrec_stateKArgs.comp hs).to_comp
  have hrem : Primrec (fun cs : CS ↦ cs.2.2.2.2.2.2) :=
    primrec_stateRem.comp hs
  have hrange : Computable (fun cs : CS ↦ List.range (cs.2.2.2.2.2.2.length + 1)) :=
    (Primrec.list_range.comp
      (Primrec.nat_add.comp (Primrec.list_length.comp hrem) (Primrec.const 1))).to_comp
  have htrav : Partrec (fun cs : CS ↦
      traversePart (loopInnerStep kCode (evalCodeAt cs.1) cs.2)
        (List.range (cs.2.2.2.2.2.2.length + 1))) :=
    (partrec_traversePart (partrec_loopInnerStep hkCode)).comp Computable.id hrange
  have hsize : Computable₂ (fun (cs : CS) (tbl : PolyCode) ↦
      sizeTableCode cs.2.2.2.2.2.2 tbl) := by
    have h1 : Primrec (fun p : CS × PolyCode ↦ p.1.2.2.2.2.2.2) := hrem.comp Primrec.fst
    exact (primrec_sizeTableCode.comp h1 Primrec.snd).to_comp.to₂
  have helse : Partrec (fun cs : CS ↦
      (traversePart (loopInnerStep kCode (evalCodeAt cs.1) cs.2)
        (List.range (cs.2.2.2.2.2.2.length + 1))).map (sizeTableCode cs.2.2.2.2.2.2)) :=
    Partrec.map htrav hsize
  exact partrec_ite_some (P := fun cs : CS ↦ cs.2.2.2.1 = 0) hcond hthen helse

theorem loopStepBody_eq_some {A : Type*}
    (kCode : A → ℕ → PolyCode → PolyCode → Code)
    (recCall : LoopState A → Part Code) (s : LoopState A)
    (ih : ∀ s', loopFuel s' < loopFuel s → recCall s' = Part.some (evalLoopState kCode s')) :
    loopStepBody kCode recCall s = Part.some (evalLoopState kCode s) := by
  rcases s with ⟨ctx, ⟨q, sq, cq⟩, ⟨fuel, c, a, r⟩⟩
  cases fuel with
  | zero =>
    rfl
  | succ n =>
    have hne : loopFuel (ctx, (q, sq, cq), (n + 1, c, a, r)) ≠ 0 := Nat.succ_ne_zero n
    change (if n + 1 = 0 then Part.some (kCode ctx c a r) else
      (traversePart (loopInnerStep kCode recCall (ctx, (q, sq, cq), (n + 1, c, a, r)))
        (List.range (r.length + 1))).map (sizeTableCode r)) =
      Part.some (pseudoDivLoopCode q sq cq (n + 1) c a r (kCode ctx))
    rw [if_neg (Nat.succ_ne_zero n)]
    have hinner (sr : ℕ) (hsr : sr ∈ List.range (r.length + 1)) :
        loopInnerStep kCode recCall (ctx, (q, sq, cq), (n + 1, c, a, r)) sr =
          Part.some (if sr < sq then kCode ctx c a r else
            leadingTableCode r (fun cr ↦
              pseudoDivLoopCode q sq cq n (c + 1)
                (quotientUpdateCodes sq sr cq cr a)
                (remainderUpdateCodes sq sr cq cr r q) (kCode ctx))) := by
      change (if sr < sq then Part.some (kCode ctx c a r) else
        (traversePart (fun j ↦ recCall (nextLoopState (ctx, (q, sq, cq), (n + 1, c, a, r)) sr j))
          (List.range (r.length + 1))).map (sizeTableCode r)) = _
      by_cases hlt : sr < sq
      · rw [if_pos hlt, if_pos hlt]
      · rw [if_neg hlt, if_neg hlt]
        have htrav : traversePart
            (fun j ↦ recCall (nextLoopState (ctx, (q, sq, cq), (n + 1, c, a, r)) sr j))
            (List.range (r.length + 1)) =
          Part.some ((List.range (r.length + 1)).map (fun j ↦
            evalLoopState kCode (nextLoopState (ctx, (q, sq, cq), (n + 1, c, a, r)) sr j))) := by
          refine traversePart_eq_some_map _ _ _ (fun j _ ↦ ?_)
          exact ih _ (loopFuel_nextLoopState_lt (ctx, (q, sq, cq), (n + 1, c, a, r)) sr j hne)
        rw [htrav, Part.map_some]
        rfl
    rw [traversePart_eq_some_map _ _ _ hinner, Part.map_some]
    rfl

theorem computable_evalLoopState {A : Type*} [Primcodable A]
    {kCode : A → ℕ → PolyCode → PolyCode → Code}
    (hkCode : Computable (fun z : A × ℕ × PolyCode × PolyCode ↦ kCode z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Computable (evalLoopState kCode) :=
  computable_of_decreasing_step (evalLoopState kCode) loopFuel (loopStepBody kCode)
    (partrec_loopStepBody hkCode) (loopStepBody_eq_some kCode)

theorem computable_pseudoDivLoopCode {A : Type*} [Primcodable A]
    {q : A → PolyCode} {sq : A → ℕ} {cq : A → Code}
    {fuel c : A → ℕ} {a r : A → PolyCode}
    {kCode : A → ℕ → PolyCode → PolyCode → Code}
    (hq : Computable q) (hsq : Computable sq) (hcq : Computable cq)
    (hfuel : Computable fuel) (hc : Computable c)
    (ha : Computable a) (hr : Computable r)
    (hkCode : Computable (fun z : A × ℕ × PolyCode × PolyCode ↦ kCode z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Computable (fun x ↦
      pseudoDivLoopCode (q x) (sq x) (cq x) (fuel x) (c x) (a x) (r x) (kCode x)) := by
  have hfx : Computable (fun x : A ↦ (q x, sq x, cq x)) :=
    hq.pair (hsq.pair hcq)
  have hvr : Computable (fun x : A ↦ (fuel x, c x, a x, r x)) :=
    hfuel.pair (hc.pair (ha.pair hr))
  have hstate : Computable (fun x : A ↦ (x, (q x, sq x, cq x), (fuel x, c x, a x, r x))) :=
    Computable.id.pair (hfx.pair hvr)
  exact ((computable_evalLoopState hkCode).comp hstate).of_eq (fun _ ↦ rfl)

theorem computable_pseudoDivCode {A : Type*} [Primcodable A]
    {p q : A → PolyCode}
    {kCode : A → ℕ → PolyCode → PolyCode → Code}
    (hp : Computable p) (hq : Computable q)
    (hkCode : Computable (fun z : A × ℕ × PolyCode × PolyCode ↦ kCode z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Computable (fun x ↦ pseudoDivCode (p x) (q x) (kCode x)) := by
  have hlead : Computable (fun z : (A × ℕ) × Code ↦
      pseudoDivLoopCode (q z.1.1) z.1.2 z.2 (p z.1.1).length 0 [] (p z.1.1) (kCode z.1.1)) := by
    have hx : Computable (fun z : (A × ℕ) × Code ↦ z.1.1) :=
      Computable.fst.comp Computable.fst
    have hsq : Computable (fun z : (A × ℕ) × Code ↦ z.1.2) :=
      Computable.snd.comp Computable.fst
    have hcq : Computable (fun z : (A × ℕ) × Code ↦ z.2) := Computable.snd
    have hp' : Computable (fun z : (A × ℕ) × Code ↦ p z.1.1) :=
      (hp.comp hx).of_eq (fun _ ↦ rfl)
    have hq' : Computable (fun z : (A × ℕ) × Code ↦ q z.1.1) :=
      (hq.comp hx).of_eq (fun _ ↦ rfl)
    have hfuel : Computable (fun z : (A × ℕ) × Code ↦ (p z.1.1).length) :=
      (Computable.list_length.comp hp').of_eq (fun _ ↦ rfl)
    have hk' : Computable (fun w : ((A × ℕ) × Code) × ℕ × PolyCode × PolyCode ↦
        kCode w.1.1.1 w.2.1 w.2.2.1 w.2.2.2) :=
      (hkCode.comp ((hx.comp Computable.fst).pair Computable.snd)).of_eq (fun _ ↦ rfl)
    exact computable_pseudoDivLoopCode hq' hsq hcq hfuel
      (Computable.const 0) (Computable.const []) hp' hk'
  have helse : Computable (fun z : A × ℕ ↦
      leadingTableCode (q z.1) (fun cq ↦
        pseudoDivLoopCode (q z.1) z.2 cq (p z.1).length 0 [] (p z.1) (kCode z.1))) :=
    computable_leadingTableCode
      (p := fun z : A × ℕ ↦ q z.1)
      (k := fun (z : A × ℕ) (cq : Code) ↦
        pseudoDivLoopCode (q z.1) z.2 cq (p z.1).length 0 [] (p z.1) (kCode z.1))
      ((hq.comp Computable.fst).of_eq (fun _ ↦ rfl)) hlead
  have hthen : Computable (fun z : A × ℕ ↦ kCode z.1 0 [] (p z.1)) :=
    (hkCode.comp (Computable.fst.pair
      ((Computable.const 0).pair ((Computable.const []).pair (hp.comp Computable.fst))))).of_eq
      (fun _ ↦ rfl)
  have hcond : Computable (fun z : A × ℕ ↦ decide (z.2 = 0)) :=
    ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide.to_comp).of_eq (fun _ ↦ rfl)
  have hbranch : Computable (fun z : A × ℕ ↦
      if z.2 = 0 then kCode z.1 0 [] (p z.1) else
        leadingTableCode (q z.1) (fun cq ↦
          pseudoDivLoopCode (q z.1) z.2 cq (p z.1).length 0 [] (p z.1) (kCode z.1))) := by
    refine (Computable.cond hcond hthen helse).of_eq (fun z ↦ ?_)
    by_cases h : z.2 = 0 <;> simp [h]
  exact computable_sizeTableCode_range (p := q)
    (k := fun (x : A) (sq : ℕ) ↦
      if sq = 0 then kCode x 0 [] (p x) else
        leadingTableCode (q x) (fun cq ↦
          pseudoDivLoopCode (q x) sq cq (p x).length 0 [] (p x) (kCode x)))
    hq hbranch

theorem computable_pseudoDivCases_code {A : Type*} [Primcodable A]
    {p q : A → TermPoly}
    {k : A → ℕ → TermPoly → TermPoly → Formula}
    {kCode : A → ℕ → PolyCode → PolyCode → Code}
    (hp : Computable (fun x ↦ (p x).map Term.code))
    (hq : Computable (fun x ↦ (q x).map Term.code))
    (hkCode : Computable (fun z : A × ℕ × PolyCode × PolyCode ↦ kCode z.1 z.2.1 z.2.2.1 z.2.2.2))
    (hk : ∀ x c a r, kCode x c (a.map Term.code) (r.map Term.code) = (k x c a r).code) :
    Computable (fun x ↦ (pseudoDivCases (p x) (q x) (k x)).code) :=
  (computable_pseudoDivCode hp hq hkCode).of_eq
    (fun x ↦ pseudoDivCode_eq (p x) (q x) (k x) (kCode x) (hk x))

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

theorem realPseudoLoop_of_lt (q : Polynomial ℝ) (fuel c : ℕ) (a r : Polynomial ℝ)
    (h : realSize r < realSize q) :
    realPseudoLoop q fuel c a r = (c, a, r) := by
  cases fuel with
  | zero => rfl
  | succ n => simp only [realPseudoLoop, if_pos h]

theorem realPseudoLoop_eq_of_size_le (q : Polynomial ℝ) (fuel c : ℕ)
    (a r : Polynomial ℝ) (hq : q ≠ 0) (hf : realSize r ≤ fuel) :
    realPseudoLoop q fuel c a r = realPseudoLoop q (realSize r) c a r := by
  induction fuel using Nat.strongRecOn generalizing c a r with
  | ind fuel ih =>
    cases fuel with
    | zero =>
      have hr0 : realSize r = 0 := Nat.eq_zero_of_le_zero hf
      rw [hr0]
    | succ n =>
      by_cases hs : realSize r < realSize q
      · rw [realPseudoLoop_of_lt q (n + 1) c a r hs,
            realPseudoLoop_of_lt q (realSize r) c a r hs]
      · have hqr : realSize q ≤ realSize r := Nat.le_of_not_gt hs
        have hq_pos : 0 < realSize q :=
          Nat.pos_of_ne_zero ((realSize_eq_zero_iff q).not.mpr hq)
        obtain ⟨m, hm⟩ : ∃ m, realSize r = m + 1 :=
          Nat.exists_eq_succ_of_ne_zero (by omega)
        let a' := Polynomial.C q.leadingCoeff * a + realReductionMonomial r q
        let r' := Polynomial.C q.leadingCoeff * r - realReductionMonomial r q * q
        have hlt : realSize r' < realSize r := realReduction_size_lt r q hq hqr
        have h1 : realPseudoLoop q (n + 1) c a r = realPseudoLoop q n (c + 1) a' r' := by
          simp only [realPseudoLoop, if_neg hs, a', r']
        have h2 : realPseudoLoop q (realSize r) c a r =
            realPseudoLoop q m (c + 1) a' r' := by
          rw [hm]
          simp only [realPseudoLoop, if_neg hs, a', r']
        have hle_n : realSize r' ≤ n := by omega
        have hle_m : realSize r' ≤ m := by omega
        have ihn := ih n (Nat.lt_succ_self n) (c + 1) a' r' hle_n
        have ihm := ih m (by omega) (c + 1) a' r' hle_m
        rw [h1, h2, ihn, ihm]

noncomputable def canonicalPseudoDiv (p q : Polynomial ℝ) :
    ℕ × Polynomial ℝ × Polynomial ℝ :=
  realPseudoDiv p q (realSize p)

theorem realPseudoDiv_eq_canonical (p q : Polynomial ℝ) (fuel : ℕ)
    (hf : realSize p ≤ fuel) :
    realPseudoDiv p q fuel = canonicalPseudoDiv p q := by
  by_cases hq : q = 0
  · simp [canonicalPseudoDiv, realPseudoDiv, realSize, hq]
  · have hs := (realSize_eq_zero_iff q).not.mpr hq
    simp only [canonicalPseudoDiv, realPseudoDiv, if_neg hs]
    exact realPseudoLoop_eq_of_size_le q fuel 0 0 p hq hf

theorem realPseudoDiv_specialize_eq_canonical (p q : TermPoly) (ρ : ℕ → ℝ) :
    realPseudoDiv (specialize ρ p) (specialize ρ q) p.length =
      canonicalPseudoDiv (specialize ρ p) (specialize ρ q) :=
  realPseudoDiv_eq_canonical _ _ _ (realSize_specialize_le_length ρ p)

theorem canonicalPseudoDiv_spec (p q : Polynomial ℝ) :
    let out := canonicalPseudoDiv p q
    Polynomial.C (q.leadingCoeff ^ out.1) * p = out.2.1 * q + out.2.2 ∧
      (q = 0 ∨ out.2.2.degree < q.degree) :=
  realPseudoDiv_spec p q (realSize p) (le_refl _)

theorem canonicalPseudoDiv_size_lt (p q : Polynomial ℝ) (hq : q ≠ 0) :
    realSize (canonicalPseudoDiv p q).2.2 < realSize q := by
  rcases canonicalPseudoDiv_spec p q with ⟨_, h0 | hdeg⟩
  · exact False.elim (hq h0)
  · exact realSize_lt_of_degree_lt _ _ hdeg

noncomputable def realNextMod (p q : Polynomial ℝ) : Polynomial ℝ :=
  -(Polynomial.C (q.leadingCoeff ^ (canonicalPseudoDiv p q).1) * (canonicalPseudoDiv p q).2.2)

theorem realNextMod_eq_of_fuel (p q : Polynomial ℝ) (fuel : ℕ)
    (hf : realSize p ≤ fuel) :
    -(Polynomial.C (q.leadingCoeff ^ (realPseudoDiv p q fuel).1) *
      (realPseudoDiv p q fuel).2.2) = realNextMod p q := by
  rw [realPseudoDiv_eq_canonical p q fuel hf]
  rfl

noncomputable def realNextModScale (p q : Polynomial ℝ) : ℝ :=
  (q.leadingCoeff ^ (canonicalPseudoDiv p q).1) ^ 2

noncomputable def realNextModQuot (p q : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (q.leadingCoeff ^ (canonicalPseudoDiv p q).1) * (canonicalPseudoDiv p q).2.1

theorem realNextModScale_pos (p q : Polynomial ℝ) (hq : q ≠ 0) :
    0 < realNextModScale p q := by
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  exact sq_pos_of_ne_zero (pow_ne_zero _ hlc)

theorem realNextMod_sturm_identity (p q : Polynomial ℝ) :
    Polynomial.C (realNextModScale p q) * p =
      realNextModQuot p q * q - realNextMod p q := by
  have hid := (canonicalPseudoDiv_spec p q).1
  unfold realNextModScale realNextModQuot realNextMod
  rw [sq, map_mul, mul_assoc, hid]
  ring

theorem realNextMod_eq_zero_iff (p q : Polynomial ℝ) (hq : q ≠ 0) :
    realNextMod p q = 0 ↔ (canonicalPseudoDiv p q).2.2 = 0 := by
  have hlc : q.leadingCoeff ^ (canonicalPseudoDiv p q).1 ≠ 0 :=
    pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hq)
  have hC : Polynomial.C (q.leadingCoeff ^ (canonicalPseudoDiv p q).1) ≠ 0 :=
    Polynomial.C_ne_zero.mpr hlc
  unfold realNextMod
  simp only [neg_eq_zero, mul_eq_zero, hC, false_or]

theorem degree_realNextMod_lt (p q : Polynomial ℝ) (hq : q ≠ 0) :
    (realNextMod p q).degree < q.degree := by
  have hlc : q.leadingCoeff ^ (canonicalPseudoDiv p q).1 ≠ 0 :=
    pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hq)
  unfold realNextMod
  rw [Polynomial.degree_neg, Polynomial.degree_mul, Polynomial.degree_C hlc, zero_add]
  rcases (canonicalPseudoDiv_spec p q).2 with h0 | hdeg
  · exact False.elim (hq h0)
  · exact hdeg

theorem realSize_realNextMod_lt (p q : Polynomial ℝ) (hq : q ≠ 0) :
    realSize (realNextMod p q) < realSize q :=
  realSize_lt_of_degree_lt _ _ (degree_realNextMod_lt p q hq)

theorem eval_realNextMod_of_eval_eq_zero (p q : Polynomial ℝ) (x : ℝ)
    (hx : q.eval x = 0) :
    (realNextMod p q).eval x = -realNextModScale p q * p.eval x := by
  have h := congrArg (Polynomial.eval x) (realNextMod_sturm_identity p q)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, hx,
    mul_zero, zero_sub] at h
  linarith

theorem eval_mul_realNextMod_neg (p q : Polynomial ℝ) (x : ℝ)
    (hq : q ≠ 0) (hx : q.eval x = 0) (hp : p.eval x ≠ 0) :
    p.eval x * (realNextMod p q).eval x < 0 := by
  rw [eval_realNextMod_of_eval_eq_zero p q x hx]
  have hpos : 0 < realNextModScale p q := realNextModScale_pos p q hq
  have hp2 : 0 < p.eval x ^ 2 := sq_pos_of_ne_zero hp
  have hprod : 0 < realNextModScale p q * p.eval x ^ 2 := mul_pos hpos hp2
  linarith [show p.eval x * (-realNextModScale p q * p.eval x) =
    -(realNextModScale p q * p.eval x ^ 2) by ring]

theorem eval_eq_zero_and_realNextMod_iff (p q : Polynomial ℝ) (x : ℝ) (hq : q ≠ 0) :
    (p.eval x = 0 ∧ q.eval x = 0) ↔
      (q.eval x = 0 ∧ (realNextMod p q).eval x = 0) := by
  have hscale : realNextModScale p q ≠ 0 := ne_of_gt (realNextModScale_pos p q hq)
  constructor
  · rintro ⟨hp, hqx⟩
    refine ⟨hqx, ?_⟩
    rw [eval_realNextMod_of_eval_eq_zero p q x hqx, hp, mul_zero]
  · rintro ⟨hqx, hm⟩
    rw [eval_realNextMod_of_eval_eq_zero p q x hqx, neg_mul, neg_eq_zero,
      mul_eq_zero] at hm
    exact ⟨hm.resolve_left hscale, hqx⟩

theorem dvd_and_dvd_realNextMod_iff (d p q : Polynomial ℝ) (hq : q ≠ 0) :
    (d ∣ p ∧ d ∣ q) ↔ (d ∣ q ∧ d ∣ realNextMod p q) := by
  have hscale : realNextModScale p q ≠ 0 := ne_of_gt (realNextModScale_pos p q hq)
  have hid := realNextMod_sturm_identity p q
  constructor
  · rintro ⟨hdp, hdq⟩
    refine ⟨hdq, ?_⟩
    have h1 : d ∣ realNextModQuot p q * q := dvd_mul_of_dvd_right hdq _
    have h2 : d ∣ Polynomial.C (realNextModScale p q) * p := dvd_mul_of_dvd_right hdp _
    have hsub : realNextMod p q =
        realNextModQuot p q * q - Polynomial.C (realNextModScale p q) * p := by
      rw [hid]
      ring
    rw [hsub]
    exact dvd_sub h1 h2
  · rintro ⟨hdq, hdm⟩
    refine ⟨?_, hdq⟩
    have h1 : d ∣ realNextModQuot p q * q := dvd_mul_of_dvd_right hdq _
    have h2 : d ∣ Polynomial.C (realNextModScale p q) * p := by
      rw [hid]
      exact dvd_sub h1 hdm
    rcases h2 with ⟨k, hk⟩
    refine ⟨Polynomial.C (realNextModScale p q)⁻¹ * k, ?_⟩
    have hinv : Polynomial.C (realNextModScale p q)⁻¹ *
        Polynomial.C (realNextModScale p q) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hscale, map_one]
    calc
      p = 1 * p := (one_mul p).symm
      _ = (Polynomial.C (realNextModScale p q)⁻¹ *
            Polynomial.C (realNextModScale p q)) * p := by rw [hinv]
      _ = Polynomial.C (realNextModScale p q)⁻¹ *
            (Polynomial.C (realNextModScale p q) * p) := by ring
      _ = Polynomial.C (realNextModScale p q)⁻¹ * (d * k) := by rw [hk]
      _ = d * (Polynomial.C (realNextModScale p q)⁻¹ * k) := by ring

noncomputable def realModsAux : ℕ → Polynomial ℝ → Polynomial ℝ → List (Polynomial ℝ)
  | 0, _, _ => []
  | n + 1, p, q =>
      if realSize p = 0 then []
      else p :: realModsAux n q (realNextMod p q)

theorem realModsAux_of_size_zero (n : ℕ) (p q : Polynomial ℝ) (hp : realSize p = 0) :
    realModsAux n p q = [] := by
  cases n with
  | zero => rfl
  | succ m => simp only [realModsAux, if_pos hp]

theorem realModsAux_of_eq_zero (n : ℕ) (q : Polynomial ℝ) :
    realModsAux n 0 q = [] :=
  realModsAux_of_size_zero n 0 q ((realSize_eq_zero_iff 0).mpr rfl)

theorem ne_zero_of_mem_realModsAux (n : ℕ) (p q f : Polynomial ℝ)
    (hf : f ∈ realModsAux n p q) : f ≠ 0 := by
  induction n generalizing p q with
  | zero => cases hf
  | succ m ih =>
    unfold realModsAux at hf
    by_cases hp : realSize p = 0
    · simp only [if_pos hp, List.not_mem_nil] at hf
    · simp only [if_neg hp, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact (realSize_eq_zero_iff f).not.mp hp
      · exact ih q (realNextMod p q) hf

theorem realModsAux_eq_of_lt (fuel : ℕ) (p q : Polynomial ℝ)
    (hqp : realSize q < realSize p) (hf : realSize p ≤ fuel) :
    realModsAux fuel p q = realModsAux (realSize p) p q := by
  induction hp_size : realSize p using Nat.strongRecOn generalizing fuel p q with
  | ind s ih =>
    have hs_pos : 0 < s := by omega
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    have hp_nz : realSize p ≠ 0 := by omega
    unfold realModsAux
    rw [if_neg hp_nz, if_neg hp_nz]
    congr 1
    by_cases hq0 : realSize q = 0
    · rw [realModsAux_of_size_zero n q _ hq0, realModsAux_of_size_zero m q _ hq0]
    · have hq_ne : q ≠ 0 := (realSize_eq_zero_iff q).not.mp hq0
      have hlt : realSize (realNextMod p q) < realSize q := realSize_realNextMod_lt p q hq_ne
      have hqm : realSize q ≤ m := by omega
      have hqn : realSize q ≤ n := by omega
      have ih1 := ih (realSize q) (by omega) n q (realNextMod p q) hlt hqn rfl
      have ih2 := ih (realSize q) (by omega) m q (realNextMod p q) hlt hqm rfl
      exact ih1.trans ih2.symm

noncomputable def realMods (p q : Polynomial ℝ) : List (Polynomial ℝ) :=
  realModsAux (realSize q + 1) p q

theorem realModsAux_eq_realMods (fuel : ℕ) (p q : Polynomial ℝ)
    (hf : realSize q + 1 ≤ fuel) :
    realModsAux fuel p q = realMods p q := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have hqn : realSize q ≤ n := by omega
  unfold realMods realModsAux
  by_cases hp0 : realSize p = 0
  · simp only [if_pos hp0]
  · simp only [if_neg hp0]
    congr 1
    by_cases hq0 : realSize q = 0
    · rw [realModsAux_of_size_zero n q _ hq0,
          realModsAux_of_size_zero (realSize q) q _ hq0]
    · have hq_ne : q ≠ 0 := (realSize_eq_zero_iff q).not.mp hq0
      exact realModsAux_eq_of_lt n q (realNextMod p q)
        (realSize_realNextMod_lt p q hq_ne) hqn

theorem realMods_zero_left (q : Polynomial ℝ) : realMods 0 q = [] :=
  realModsAux_of_eq_zero (realSize q + 1) q

theorem realMods_cons (p q : Polynomial ℝ) (hp : p ≠ 0) :
    realMods p q = p :: realMods q (realNextMod p q) := by
  have hp0 : realSize p ≠ 0 := (realSize_eq_zero_iff p).not.mpr hp
  unfold realMods
  conv_lhs => unfold realModsAux
  rw [if_neg hp0]
  congr 1
  by_cases hq : q = 0
  · subst hq
    rw [realModsAux_of_eq_zero, realModsAux_of_eq_zero]
  · have hlt : realSize (realNextMod p q) + 1 ≤ realSize q :=
      realSize_realNextMod_lt p q hq
    exact realModsAux_eq_realMods (realSize q) q (realNextMod p q) hlt

theorem ne_zero_of_mem_realMods (p q f : Polynomial ℝ)
    (hf : f ∈ realMods p q) : f ≠ 0 :=
  ne_zero_of_mem_realModsAux (realSize q + 1) p q f hf

noncomputable def realChanges : List ℝ → ℕ
  | [] => 0
  | a :: xs =>
      (haveI := Classical.propDecidable; if a * xs.headD 0 < 0 then 1 else 0) +
        realChanges xs

@[simp] theorem realChanges_nil : realChanges [] = 0 := rfl

@[simp] theorem realChanges_singleton (a : ℝ) : realChanges [a] = 0 := by
  classical
  simp [realChanges]

theorem realChanges_cons_cons (a b : ℝ) (xs : List ℝ) :
    realChanges (a :: b :: xs) =
      (haveI := Classical.propDecidable; if a * b < 0 then 1 else 0) +
        realChanges (b :: xs) := rfl

noncomputable def signVariations (xs : List ℝ) : ℕ := by
  classical
  exact realChanges (xs.filter (fun x ↦ decide (x ≠ 0)))

theorem signVariations_eq_realChanges (xs : List ℝ) (h : ∀ x ∈ xs, x ≠ 0) :
    signVariations xs = realChanges xs := by
  classical
  unfold signVariations
  have hfilt : xs.filter (fun x ↦ decide (x ≠ 0)) = xs :=
    List.filter_eq_self.mpr (fun x hx ↦ decide_eq_true (h x hx))
  rw [hfilt]

@[simp] theorem signVariations_nil : signVariations [] = 0 := by
  classical
  simp [signVariations]

@[simp] theorem signVariations_zero_cons (xs : List ℝ) :
    signVariations (0 :: xs) = signVariations xs := by
  classical
  simp [signVariations]

theorem signVariations_cons_zero_cons (a : ℝ) (xs : List ℝ) :
    signVariations (a :: 0 :: xs) = signVariations (a :: xs) := by
  classical
  by_cases ha : a = 0 <;> simp [signVariations, ha]

theorem signVariations_cons_cons_of_mul_neg (a b c : ℝ) (xs : List ℝ)
    (hac : a * c < 0) :
    signVariations (a :: b :: c :: xs) = 1 + signVariations (c :: xs) := by
  classical
  have ha : a ≠ 0 := fun h ↦ by simp [h] at hac
  have hc : c ≠ 0 := fun h ↦ by simp [h] at hac
  by_cases hb : b = 0
  · subst hb
    simp only [signVariations, List.filter, decide_eq_true ha, decide_eq_true hc,
      ne_self_iff_false, decide_false]
    rw [realChanges_cons_cons, if_pos hac]
  · simp only [signVariations, List.filter, decide_eq_true ha,
      decide_eq_true hb, decide_eq_true hc]
    rw [realChanges_cons_cons, realChanges_cons_cons, ← add_assoc]
    congr 1
    have hprod : (a * b) * (b * c) < 0 := by
      have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
      have hneg : b ^ 2 * (a * c) < 0 := mul_neg_of_pos_of_neg hb2 hac
      linarith [show (a * b) * (b * c) = b ^ 2 * (a * c) by ring]
    by_cases hab : a * b < 0
    · have hbc : ¬ b * c < 0 := by
        intro hbc
        have := mul_pos_of_neg_of_neg hab hbc
        linarith
      simp only [if_pos hab, if_neg hbc, add_zero]
    · have hab_pos : 0 < a * b := by
        have hab_ne : a * b ≠ 0 := mul_ne_zero ha hb
        exact lt_of_le_of_ne (not_lt.mp hab) hab_ne.symm
      have hbc : b * c < 0 := by
        by_contra hbc
        have := mul_nonneg (le_of_lt hab_pos) (not_lt.mp hbc)
        linarith
      simp only [if_neg hab, if_pos hbc, zero_add]

noncomputable def minftySignFactor (s : ℕ) : ℝ := (-1 : ℝ) ^ (s - 1)

noncomputable def minftyCoeff (p : Polynomial ℝ) : ℝ :=
  minftySignFactor (realSize p) * p.leadingCoeff

theorem minftyCoeff_zero : minftyCoeff 0 = 0 := by
  simp [minftyCoeff]

theorem minftyCoeff_eq_of_ne_zero (p : Polynomial ℝ) (hp : p ≠ 0) :
    minftyCoeff p = (-1 : ℝ) ^ p.natDegree * p.leadingCoeff := by
  classical
  simp only [minftyCoeff, minftySignFactor, realSize, if_neg hp, Nat.add_sub_cancel]

theorem minftyCoeff_ne_zero (p : Polynomial ℝ) (hp : p ≠ 0) :
    minftyCoeff p ≠ 0 := by
  rw [minftyCoeff_eq_of_ne_zero p hp]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Polynomial.leadingCoeff_ne_zero.mpr hp)

noncomputable def realSeqPInfty (ps : List (Polynomial ℝ)) : List ℝ :=
  ps.map Polynomial.leadingCoeff

noncomputable def realSeqMInfty (ps : List (Polynomial ℝ)) : List ℝ :=
  ps.map minftyCoeff

noncomputable def realChangesPoly (ps : List (Polynomial ℝ)) : ℤ :=
  (realChanges (realSeqMInfty ps) : ℤ) - (realChanges (realSeqPInfty ps) : ℤ)

theorem realSeqPInfty_ne_zero_of_ne_zero (ps : List (Polynomial ℝ))
    (hps : ∀ p ∈ ps, p ≠ 0) :
    ∀ x ∈ realSeqPInfty ps, x ≠ 0 := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
  exact Polynomial.leadingCoeff_ne_zero.mpr (hps p hp)

theorem realSeqMInfty_ne_zero_of_ne_zero (ps : List (Polynomial ℝ))
    (hps : ∀ p ∈ ps, p ≠ 0) :
    ∀ x ∈ realSeqMInfty ps, x ≠ 0 := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
  exact minftyCoeff_ne_zero p (hps p hp)

theorem realChangesPoly_eq_signVariations (ps : List (Polynomial ℝ))
    (hps : ∀ p ∈ ps, p ≠ 0) :
    realChangesPoly ps =
      (signVariations (realSeqMInfty ps) : ℤ) -
        (signVariations (realSeqPInfty ps) : ℤ) := by
  rw [signVariations_eq_realChanges _ (realSeqMInfty_ne_zero_of_ne_zero ps hps),
      signVariations_eq_realChanges _ (realSeqPInfty_ne_zero_of_ne_zero ps hps)]
  rfl

theorem realChangesPoly_realMods_eq_signVariations (p q : Polynomial ℝ) :
    realChangesPoly (realMods p q) =
      (signVariations (realSeqMInfty (realMods p q)) : ℤ) -
        (signVariations (realSeqPInfty (realMods p q)) : ℤ) :=
  realChangesPoly_eq_signVariations (realMods p q) (ne_zero_of_mem_realMods p q)

end Grunbaum2003.FormulaCompiler.Parametric

open scoped BigOperators

namespace Grunbaum2003.FormulaCompiler.Parametric

noncomputable def realSign (x : ℝ) : ℤ :=
  haveI := Classical.propDecidable
  if 0 < x then 1 else if x < 0 then -1 else 0

@[simp] theorem realSign_zero : realSign 0 = 0 := by
  classical
  simp [realSign]

theorem realSign_pos {x : ℝ} (h : 0 < x) : realSign x = 1 := by
  classical
  simp [realSign, h]

theorem realSign_neg {x : ℝ} (h : x < 0) : realSign x = -1 := by
  classical
  have hnp : ¬ 0 < x := not_lt.mpr (le_of_lt h)
  simp [realSign, hnp, h]

theorem realSign_eq_zero_iff (x : ℝ) : realSign x = 0 ↔ x = 0 := by
  rcases lt_trichotomy 0 x with h | rfl | h
  · simp [realSign_pos h, ne_of_gt h]
  · simp
  · simp [realSign_neg h, ne_of_lt h]

theorem realSign_ne_zero_iff (x : ℝ) : realSign x ≠ 0 ↔ x ≠ 0 :=
  (realSign_eq_zero_iff x).not

theorem realSign_neg_val (x : ℝ) : realSign (-x) = -realSign x := by
  rcases lt_trichotomy 0 x with h | rfl | h
  · rw [realSign_pos h, realSign_neg (neg_lt_zero.mpr h)]
  · simp
  · rw [realSign_neg h, realSign_pos (neg_pos.mpr h), neg_neg]

theorem realSign_mul (x y : ℝ) : realSign (x * y) = realSign x * realSign y := by
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · rcases lt_trichotomy 0 y with hy | rfl | hy
    · rw [realSign_pos hx, realSign_pos hy, realSign_pos (mul_pos hx hy), mul_one]
    · simp
    · rw [realSign_pos hx, realSign_neg hy, realSign_neg (mul_neg_of_pos_of_neg hx hy), one_mul]
  · simp
  · rcases lt_trichotomy 0 y with hy | rfl | hy
    · rw [realSign_neg hx, realSign_pos hy, realSign_neg (mul_neg_of_neg_of_pos hx hy), mul_one]
    · simp
    · rw [realSign_neg hx, realSign_neg hy, realSign_pos (mul_pos_of_neg_of_neg hx hy)]
      ring

theorem realSign_pow (x : ℝ) (n : ℕ) : realSign (x ^ n) = realSign x ^ n := by
  induction n with
  | zero => simp [realSign_pos zero_lt_one]
  | succ m ih => rw [pow_succ, pow_succ, realSign_mul, ih]

@[simp] theorem realSign_neg_one : realSign (-1 : ℝ) = -1 :=
  realSign_neg (by norm_num)

@[simp] theorem realSign_one : realSign (1 : ℝ) = 1 :=
  realSign_pos zero_lt_one

theorem realSign_neg_one_pow (n : ℕ) : realSign ((-1 : ℝ) ^ n) = (-1 : ℤ) ^ n := by
  rw [realSign_pow, realSign_neg_one]

theorem realSign_sq_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    realSign x * realSign x = 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [realSign_neg h]; rfl
  · rw [realSign_pos h]; rfl

theorem realSign_mul_of_pos {c x : ℝ} (hc : 0 < c) :
    realSign (c * x) = realSign x := by
  rw [realSign_mul, realSign_pos hc, one_mul]

theorem realSign_mul_of_neg {c x : ℝ} (hc : c < 0) :
    realSign (c * x) = -realSign x := by
  rw [realSign_mul, realSign_neg hc, neg_one_mul]

theorem two_mul_ite_neg_sub {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (haveI := Classical.propDecidable
     2 * ((if u < 0 then (1 : ℤ) else 0) - (if v < 0 then (1 : ℤ) else 0))) =
      realSign v - realSign u := by
  classical
  rcases lt_or_gt_of_ne hu with h1 | h1 <;> rcases lt_or_gt_of_ne hv with h2 | h2
  · simp [h1, h2, realSign_neg h1, realSign_neg h2]
  · simp [h1, not_lt.mpr (le_of_lt h2), realSign_neg h1, realSign_pos h2]
  · simp [not_lt.mpr (le_of_lt h1), h2, realSign_pos h1, realSign_neg h2]
  · simp [not_lt.mpr (le_of_lt h1), not_lt.mpr (le_of_lt h2), realSign_pos h1, realSign_pos h2]

noncomputable def shiftPoly (p : Polynomial ℝ) (t : ℝ) : Polynomial ℝ :=
  p.comp (Polynomial.X + Polynomial.C t)

@[simp] theorem shiftPoly_zero (t : ℝ) : shiftPoly 0 t = 0 :=
  Polynomial.zero_comp

@[simp] theorem shiftPoly_eq_zero_iff (p : Polynomial ℝ) (t : ℝ) :
    shiftPoly p t = 0 ↔ p = 0 :=
  Polynomial.comp_X_add_C_eq_zero_iff

theorem shiftPoly_mul (p q : Polynomial ℝ) (t : ℝ) :
    shiftPoly (p * q) t = shiftPoly p t * shiftPoly q t :=
  Polynomial.mul_comp p q (Polynomial.X + Polynomial.C t)

theorem shiftPoly_C (c t : ℝ) : shiftPoly (Polynomial.C c) t = Polynomial.C c :=
  Polynomial.C_comp

theorem shiftPoly_X_sub_C_self (t : ℝ) :
    shiftPoly (Polynomial.X - Polynomial.C t) t = Polynomial.X := by
  simp [shiftPoly]

theorem coeff_zero_shiftPoly (p : Polynomial ℝ) (t : ℝ) :
    (shiftPoly p t).coeff 0 = p.eval t := by
  rw [Polynomial.coeff_zero_eq_eval_zero, shiftPoly, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]

theorem rootMultiplicity_eq_natTrailingDegree_shiftPoly (p : Polynomial ℝ) (t : ℝ) :
    p.rootMultiplicity t = (shiftPoly p t).natTrailingDegree :=
  Polynomial.rootMultiplicity_eq_natTrailingDegree

theorem derivative_shiftPoly (p : Polynomial ℝ) (t : ℝ) :
    (shiftPoly p t).derivative = shiftPoly p.derivative t := by
  simp [shiftPoly, Polynomial.derivative_comp]

noncomputable def germRight (p : Polynomial ℝ) (t : ℝ) : ℝ :=
  (shiftPoly p t).trailingCoeff

noncomputable def germLeft (p : Polynomial ℝ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ p.rootMultiplicity t * germRight p t

@[simp] theorem germRight_zero (t : ℝ) : germRight 0 t = 0 := by
  simp [germRight]

@[simp] theorem germLeft_zero (t : ℝ) : germLeft 0 t = 0 := by
  simp [germLeft]

@[simp] theorem germRight_eq_zero_iff (p : Polynomial ℝ) (t : ℝ) :
    germRight p t = 0 ↔ p = 0 := by
  rw [germRight, Polynomial.trailingCoeff_eq_zero, shiftPoly_eq_zero_iff]

theorem germRight_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (t : ℝ) :
    germRight p t ≠ 0 :=
  (germRight_eq_zero_iff p t).not.mpr hp

@[simp] theorem germLeft_eq_zero_iff (p : Polynomial ℝ) (t : ℝ) :
    germLeft p t = 0 ↔ p = 0 := by
  simp [germLeft, pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)]

theorem germLeft_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (t : ℝ) :
    germLeft p t ≠ 0 :=
  (germLeft_eq_zero_iff p t).not.mpr hp

theorem trailingCoeff_mul_real (f g : Polynomial ℝ) :
    (f * g).trailingCoeff = f.trailingCoeff * g.trailingCoeff := by
  by_cases hf : f = 0
  · simp [hf]
  · by_cases hg : g = 0
    · simp [hg]
    · rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_mul hf hg,
          Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree]

theorem germRight_mul (p q : Polynomial ℝ) (t : ℝ) :
    germRight (p * q) t = germRight p t * germRight q t := by
  rw [germRight, shiftPoly_mul, trailingCoeff_mul_real]
  rfl

theorem germRight_pow (p : Polynomial ℝ) (n : ℕ) (t : ℝ) :
    germRight (p ^ n) t = germRight p t ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, germRight, shiftPoly, Polynomial.one_comp,
      Polynomial.trailingCoeff, Polynomial.natTrailingDegree_one, Polynomial.coeff_one_zero]
  | succ m ih => rw [pow_succ, pow_succ, germRight_mul, ih]

theorem germLeft_mul {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (t : ℝ) :
    germLeft (p * q) t = germLeft p t * germLeft q t := by
  unfold germLeft
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hp hq), pow_add, germRight_mul]
  ring

theorem germRight_of_eval_ne_zero {p : Polynomial ℝ} {t : ℝ} (h : p.eval t ≠ 0) :
    germRight p t = p.eval t := by
  have hc0 : (shiftPoly p t).coeff 0 ≠ 0 := by rwa [coeff_zero_shiftPoly]
  rw [germRight, Polynomial.trailingCoeff_eq_coeff_zero hc0, coeff_zero_shiftPoly]

theorem germLeft_of_eval_ne_zero {p : Polynomial ℝ} {t : ℝ} (h : p.eval t ≠ 0) :
    germLeft p t = p.eval t := by
  have hnr : ¬ p.IsRoot t := h
  rw [germLeft, Polynomial.rootMultiplicity_eq_zero hnr, pow_zero, one_mul,
      germRight_of_eval_ne_zero h]

@[simp] theorem germRight_X_sub_C_self (t : ℝ) :
    germRight (Polynomial.X - Polynomial.C t) t = 1 := by
  rw [germRight, shiftPoly_X_sub_C_self, Polynomial.trailingCoeff,
      Polynomial.natTrailingDegree_X, Polynomial.coeff_X_one]

theorem natTrailingDegree_eq_of_coeff_ne_zero {f : Polynomial ℝ} {n : ℕ}
    (hn : f.coeff n ≠ 0) (h0 : ∀ i < n, f.coeff i = 0) :
    f.natTrailingDegree = n := by
  have hf : f ≠ 0 := fun h ↦ hn (by simp [h])
  exact le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hn)
    (Polynomial.le_natTrailingDegree hf h0)

theorem trailingCoeff_eq_of_coeff_ne_zero {f : Polynomial ℝ} {n : ℕ}
    (hn : f.coeff n ≠ 0) (h0 : ∀ i < n, f.coeff i = 0) :
    f.trailingCoeff = f.coeff n := by
  rw [Polynomial.trailingCoeff, natTrailingDegree_eq_of_coeff_ne_zero hn h0]

theorem rootMultiplicity_and_germRight_derivative {p : Polynomial ℝ} {t : ℝ}
    (hp : p ≠ 0) (ht : p.IsRoot t) :
    p.derivative.rootMultiplicity t = p.rootMultiplicity t - 1 ∧
      germRight p.derivative t = (p.rootMultiplicity t : ℝ) * germRight p t := by
  let f := shiftPoly p t
  let m := p.rootMultiplicity t
  have hm_pos : 0 < m := (Polynomial.rootMultiplicity_pos hp).mpr ht
  have hm_eq : f.natTrailingDegree = m :=
    (rootMultiplicity_eq_natTrailingDegree_shiftPoly p t).symm
  have htc : f.coeff m = germRight p t := by
    change f.coeff m = f.trailingCoeff
    rw [Polynomial.trailingCoeff, hm_eq]
  have htc_ne : germRight p t ≠ 0 := germRight_ne_zero hp t
  have hm_real_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm_pos)
  have hcoeff_m1 : f.derivative.coeff (m - 1) = (m : ℝ) * germRight p t := by
    rw [Polynomial.coeff_derivative]
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
    have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hm1
    rw [hm1, htc, hcast, mul_comm]
  have hne : f.derivative.coeff (m - 1) ≠ 0 := by
    rw [hcoeff_m1]
    exact mul_ne_zero hm_real_ne htc_ne
  have hzero : ∀ i < m - 1, f.derivative.coeff i = 0 := by
    intro i hi
    rw [Polynomial.coeff_derivative]
    have hi1 : i + 1 < f.natTrailingDegree := by omega
    rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi1, zero_mul]
  have hntd := natTrailingDegree_eq_of_coeff_ne_zero hne hzero
  have htr := trailingCoeff_eq_of_coeff_ne_zero hne hzero
  refine ⟨?_, ?_⟩
  · rw [rootMultiplicity_eq_natTrailingDegree_shiftPoly, ← derivative_shiftPoly, hntd]
  · rw [germRight, ← derivative_shiftPoly, htr, hcoeff_m1]

theorem coeff_mul_eq_zero_of_lt_natTrailingDegree_right (a q : Polynomial ℝ) {i : ℕ}
    (hi : i < q.natTrailingDegree) :
    (a * q).coeff i = 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero ?_
  rintro ⟨u, v⟩ huv
  rw [Finset.mem_antidiagonal] at huv
  have hv : v < q.natTrailingDegree := by omega
  rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hv, mul_zero]

theorem rootMultiplicity_and_germRight_realNextMod {p q : Polynomial ℝ} {t : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hlt : p.rootMultiplicity t < q.rootMultiplicity t) :
    (realNextMod p q).rootMultiplicity t = p.rootMultiplicity t ∧
      germRight (realNextMod p q) t = -realNextModScale p q * germRight p t ∧
      realNextMod p q ≠ 0 := by
  have hid := congrArg (fun f ↦ shiftPoly f t) (realNextMod_sturm_identity p q)
  simp only [shiftPoly, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp] at hid
  change Polynomial.C (realNextModScale p q) * shiftPoly p t =
    shiftPoly (realNextModQuot p q) t * shiftPoly q t - shiftPoly (realNextMod p q) t at hid
  have hR_eq : shiftPoly (realNextMod p q) t =
      shiftPoly (realNextModQuot p q) t * shiftPoly q t -
        Polynomial.C (realNextModScale p q) * shiftPoly p t := by
    rw [hid]; ring
  let m := p.rootMultiplicity t
  have hm_eq : (shiftPoly p t).natTrailingDegree = m :=
    (rootMultiplicity_eq_natTrailingDegree_shiftPoly p t).symm
  have hq_eq : (shiftPoly q t).natTrailingDegree = q.rootMultiplicity t :=
    (rootMultiplicity_eq_natTrailingDegree_shiftPoly q t).symm
  have hcoeff_le : ∀ i ≤ m,
      (shiftPoly (realNextMod p q) t).coeff i =
        -realNextModScale p q * (shiftPoly p t).coeff i := by
    intro i hi
    have hi_q : i < (shiftPoly q t).natTrailingDegree := by omega
    rw [hR_eq, Polynomial.coeff_sub,
        coeff_mul_eq_zero_of_lt_natTrailingDegree_right _ _ hi_q,
        Polynomial.coeff_C_mul, zero_sub, neg_mul]
  have hScale_pos : 0 < realNextModScale p q := realNextModScale_pos p q hq
  have htc : (shiftPoly p t).coeff m = germRight p t := by
    change (shiftPoly p t).coeff m = (shiftPoly p t).trailingCoeff
    rw [Polynomial.trailingCoeff, hm_eq]
  have hcoeff_m : (shiftPoly (realNextMod p q) t).coeff m =
      -realNextModScale p q * germRight p t := by
    rw [hcoeff_le m (le_refl m), htc]
  have hne : (shiftPoly (realNextMod p q) t).coeff m ≠ 0 := by
    rw [hcoeff_m]
    exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hScale_pos)) (germRight_ne_zero hp t)
  have hzero : ∀ i < m, (shiftPoly (realNextMod p q) t).coeff i = 0 := by
    intro i hi
    rw [hcoeff_le i (le_of_lt hi)]
    have hi' : i < (shiftPoly p t).natTrailingDegree := by omega
    rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi', mul_zero]
  have hntd := natTrailingDegree_eq_of_coeff_ne_zero hne hzero
  have htr := trailingCoeff_eq_of_coeff_ne_zero hne hzero
  have hr_ne : realNextMod p q ≠ 0 := by
    intro h0
    rw [h0, shiftPoly_zero, Polynomial.coeff_zero] at hne
    exact hne rfl
  refine ⟨?_, ?_, hr_ne⟩
  · rw [rootMultiplicity_eq_natTrailingDegree_shiftPoly, hntd]
  · rw [germRight, htr, hcoeff_m]

noncomputable def cauchyJump (p q : Polynomial ℝ) (t : ℝ) : ℤ :=
  haveI := Classical.propDecidable
  if p ≠ 0 ∧ q ≠ 0 ∧ q.rootMultiplicity t < p.rootMultiplicity t ∧
      Odd (p.rootMultiplicity t - q.rootMultiplicity t) then
    realSign (germRight p t * germRight q t)
  else 0

@[simp] theorem cauchyJump_zero_left (q : Polynomial ℝ) (t : ℝ) :
    cauchyJump 0 q t = 0 := by
  classical
  simp [cauchyJump]

@[simp] theorem cauchyJump_zero_right (p : Polynomial ℝ) (t : ℝ) :
    cauchyJump p 0 t = 0 := by
  classical
  simp [cauchyJump]

theorem cauchyJump_eq_zero_of_not_mem_roots {p q : Polynomial ℝ} {t : ℝ}
    (ht : t ∉ p.roots.toFinset) : cauchyJump p q t = 0 := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  · have hnr : ¬ p.IsRoot t := by
      intro hr
      exact ht (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hr))
    have hm0 : p.rootMultiplicity t = 0 := Polynomial.rootMultiplicity_eq_zero hnr
    simp [cauchyJump, hm0]

noncomputable def cauchyIndex (p q : Polynomial ℝ) : ℤ :=
  ∑ t ∈ p.roots.toFinset, cauchyJump p q t

@[simp] theorem cauchyIndex_zero_left (q : Polynomial ℝ) : cauchyIndex 0 q = 0 := by
  simp [cauchyIndex]

@[simp] theorem cauchyIndex_zero_right (p : Polynomial ℝ) : cauchyIndex p 0 = 0 := by
  simp [cauchyIndex]

theorem cauchyIndex_eq_sum_of_subset (p q : Polynomial ℝ) (S : Finset ℝ)
    (hS : p.roots.toFinset ⊆ S) :
    cauchyIndex p q = ∑ t ∈ S, cauchyJump p q t := by
  unfold cauchyIndex
  exact Finset.sum_subset hS (fun t _ ht ↦ cauchyJump_eq_zero_of_not_mem_roots ht)

noncomputable def tarskiQueryR (p q : Polynomial ℝ) : ℤ :=
  ∑ x ∈ p.roots.toFinset, realSign (q.eval x)

@[simp] theorem tarskiQueryR_zero_left (q : Polynomial ℝ) : tarskiQueryR 0 q = 0 := by
  simp [tarskiQueryR]

theorem cauchyJump_derivative_mul {p : Polynomial ℝ} (q : Polynomial ℝ) {t : ℝ}
    (hp : p ≠ 0) (ht : p.IsRoot t) :
    cauchyJump p (p.derivative * q) t = realSign (q.eval t) := by
  classical
  rcases rootMultiplicity_and_germRight_derivative hp ht with ⟨hdm, hdg⟩
  have hm_pos : 0 < p.rootMultiplicity t := (Polynomial.rootMultiplicity_pos hp).mpr ht
  have hp' : p.derivative ≠ 0 := by
    intro h0
    have h := germRight_ne_zero hp t
    have hm_ne : (p.rootMultiplicity t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm_pos)
    rw [h0, germRight_zero] at hdg
    exact mul_ne_zero hm_ne h hdg.symm
  by_cases hqt : q.eval t = 0
  · rw [hqt, realSign_zero]
    by_cases hq : q = 0
    · simp [hq]
    · have hq_pos : 0 < q.rootMultiplicity t :=
        (Polynomial.rootMultiplicity_pos hq).mpr hqt
      have hmul_ne : p.derivative * q ≠ 0 := mul_ne_zero hp' hq
      have hrm : (p.derivative * q).rootMultiplicity t =
          p.rootMultiplicity t - 1 + q.rootMultiplicity t := by
        rw [Polynomial.rootMultiplicity_mul hmul_ne, hdm]
      have hnlt : ¬ (p.derivative * q).rootMultiplicity t < p.rootMultiplicity t := by omega
      simp [cauchyJump, hnlt]
  · have hq : q ≠ 0 := fun h0 ↦ hqt (by simp [h0])
    have hmul_ne : p.derivative * q ≠ 0 := mul_ne_zero hp' hq
    have hq_rm : q.rootMultiplicity t = 0 := Polynomial.rootMultiplicity_eq_zero hqt
    have hrm : (p.derivative * q).rootMultiplicity t = p.rootMultiplicity t - 1 := by
      rw [Polynomial.rootMultiplicity_mul hmul_ne, hdm, hq_rm, add_zero]
    have hlt : (p.derivative * q).rootMultiplicity t < p.rootMultiplicity t := by omega
    have hsub : p.rootMultiplicity t - (p.derivative * q).rootMultiplicity t = 1 := by omega
    have hodd : Odd (p.rootMultiplicity t - (p.derivative * q).rootMultiplicity t) := by
      rw [hsub]; exact odd_one
    unfold cauchyJump
    rw [if_pos ⟨hp, hmul_ne, hlt, hodd⟩]
    rw [germRight_mul, hdg, germRight_of_eval_ne_zero hqt]
    have hpos : 0 < (p.rootMultiplicity t : ℝ) := Nat.cast_pos.mpr hm_pos
    have hsq : realSign (germRight p t) * realSign (germRight p t) = 1 :=
      realSign_sq_of_ne_zero (germRight_ne_zero hp t)
    calc
      realSign (germRight p t * ((p.rootMultiplicity t : ℝ) * germRight p t * q.eval t))
        = realSign ((p.rootMultiplicity t : ℝ) *
            (germRight p t * germRight p t * q.eval t)) := by ring_nf
      _ = realSign (germRight p t * germRight p t * q.eval t) := realSign_mul_of_pos hpos
      _ = realSign (germRight p t) * realSign (germRight p t) * realSign (q.eval t) := by
            rw [realSign_mul, realSign_mul]
      _ = realSign (q.eval t) := by rw [hsq, one_mul]

theorem cauchyIndex_derivative_mul (p q : Polynomial ℝ) :
    cauchyIndex p (p.derivative * q) = tarskiQueryR p q := by
  by_cases hp : p = 0
  · simp [hp]
  · unfold cauchyIndex tarskiQueryR
    refine Finset.sum_congr rfl ?_
    intro t ht
    have hr : p.IsRoot t := (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp ht)
    exact cauchyJump_derivative_mul q hp hr

theorem cauchyJump_realNextMod {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (t : ℝ) :
    cauchyJump q (realNextMod p q) t = -cauchyJump q p t := by
  classical
  by_cases hlt : p.rootMultiplicity t < q.rootMultiplicity t
  · rcases rootMultiplicity_and_germRight_realNextMod hp hq hlt with ⟨hrm, hg, hr_ne⟩
    have hlt' : (realNextMod p q).rootMultiplicity t < q.rootMultiplicity t := by
      rwa [hrm]
    unfold cauchyJump
    rw [hrm]
    by_cases hodd : Odd (q.rootMultiplicity t - p.rootMultiplicity t)
    · rw [if_pos ⟨hq, hr_ne, hlt, hodd⟩, if_pos ⟨hq, hp, hlt, hodd⟩, hg]
      have hneg : -realNextModScale p q < 0 :=
        neg_lt_zero.mpr (realNextModScale_pos p q hq)
      calc
        realSign (germRight q t * (-realNextModScale p q * germRight p t))
          = realSign (-realNextModScale p q * (germRight q t * germRight p t)) := by ring_nf
        _ = -realSign (germRight q t * germRight p t) := realSign_mul_of_neg hneg
    · rw [if_neg (by tauto), if_neg (by tauto), neg_zero]
  · by_cases hr0 : realNextMod p q = 0
    · simp [cauchyJump, hr0, hlt]
    · have hnlt' : ¬ (realNextMod p q).rootMultiplicity t < q.rootMultiplicity t := by
        intro hlt'
        have hq_le : q.rootMultiplicity t ≤ p.rootMultiplicity t := not_lt.mp hlt
        have hdvd_p : (Polynomial.X - Polynomial.C t) ^ q.rootMultiplicity t ∣ p :=
          (Polynomial.le_rootMultiplicity_iff hp).mp hq_le
        have hdvd_q : (Polynomial.X - Polynomial.C t) ^ q.rootMultiplicity t ∣ q :=
          Polynomial.pow_rootMultiplicity_dvd q t
        have hdvd_r : (Polynomial.X - Polynomial.C t) ^ q.rootMultiplicity t ∣
            realNextMod p q :=
          ((dvd_and_dvd_realNextMod_iff _ p q hq).mp ⟨hdvd_p, hdvd_q⟩).2
        have hle_r : q.rootMultiplicity t ≤ (realNextMod p q).rootMultiplicity t :=
          (Polynomial.le_rootMultiplicity_iff hr0).mpr hdvd_r
        omega
      simp [cauchyJump, hlt, hnlt']

theorem cauchyIndex_realNextMod {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    cauchyIndex q (realNextMod p q) = -cauchyIndex q p := by
  unfold cauchyIndex
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro t _
  exact cauchyJump_realNextMod hp hq t

noncomputable def singleRootJump (f : Polynomial ℝ) (t : ℝ) : ℤ :=
  haveI := Classical.propDecidable
  (if germLeft f t < 0 then 1 else 0) - (if germRight f t < 0 then 1 else 0)

theorem two_mul_singleRootJump {f : Polynomial ℝ} (hf : f ≠ 0) (t : ℝ) :
    2 * singleRootJump f t = realSign (germRight f t) - realSign (germLeft f t) :=
  two_mul_ite_neg_sub (germLeft_ne_zero hf t) (germRight_ne_zero hf t)

theorem realSign_germLeft (f : Polynomial ℝ) (t : ℝ) :
    realSign (germLeft f t) = (-1 : ℤ) ^ f.rootMultiplicity t * realSign (germRight f t) := by
  rw [germLeft, realSign_mul, realSign_neg_one_pow]

theorem cauchyJump_add_symm {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (t : ℝ) :
    cauchyJump p q t + cauchyJump q p t = singleRootJump (p * q) t := by
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  suffices h2 : 2 * (cauchyJump p q t + cauchyJump q p t) = 2 * singleRootJump (p * q) t by
    omega
  rw [two_mul_singleRootJump hpq t, realSign_germLeft,
      Polynomial.rootMultiplicity_mul hpq, germRight_mul]
  let m := p.rootMultiplicity t
  let k := q.rootMultiplicity t
  have hs_comm : realSign (germRight q t * germRight p t) =
      realSign (germRight p t * germRight q t) := by
    rw [mul_comm]
  unfold cauchyJump
  rw [hs_comm]
  rcases Nat.even_or_odd (m + k) with heven | hodd
  · have hno1 : ¬ (p ≠ 0 ∧ q ≠ 0 ∧ k < m ∧ Odd (m - k)) := by
      rintro ⟨_, _, hkm, hod⟩
      have hsum : m + k = (m - k) + 2 * k := by omega
      have : Odd (m + k) := by
        rw [hsum]
        exact Odd.add_even hod (even_two_mul k)
      exact (Nat.not_even_iff_odd.mpr this) heven
    have hno2 : ¬ (q ≠ 0 ∧ p ≠ 0 ∧ m < k ∧ Odd (k - m)) := by
      rintro ⟨_, _, hmk, hod⟩
      have hsum : m + k = (k - m) + 2 * m := by omega
      have : Odd (m + k) := by
        rw [hsum]
        exact Odd.add_even hod (even_two_mul m)
      exact (Nat.not_even_iff_odd.mpr this) heven
    rw [if_neg hno1, if_neg hno2, Even.neg_one_pow heven, one_mul, sub_self,
        add_zero, mul_zero]
  · rw [Odd.neg_one_pow hodd, neg_one_mul, sub_neg_eq_add, ← two_mul]
    rcases lt_trichotomy k m with hkm | hkm | hmk
    · have hod1 : Odd (m - k) := by
        have hsum : m + k = (m - k) + 2 * k := by omega
        rcases Nat.even_or_odd (m - k) with hev | hod
        · exfalso
          have : Even (m + k) := by rw [hsum]; exact Even.add hev (even_two_mul k)
          exact (Nat.not_even_iff_odd.mpr hodd) this
        · exact hod
      have hnmk : ¬ (q ≠ 0 ∧ p ≠ 0 ∧ m < k ∧ Odd (k - m)) := by
        rintro ⟨_, _, hmk, _⟩
        exact (not_lt.mpr (le_of_lt hkm)) hmk
      rw [if_pos ⟨hp, hq, hkm, hod1⟩, if_neg hnmk, add_zero]
    · exfalso
      have : Even (m + k) := by rw [hkm, ← two_mul]; exact even_two_mul m
      exact (Nat.not_even_iff_odd.mpr hodd) this
    · have hod2 : Odd (k - m) := by
        have hsum : m + k = (k - m) + 2 * m := by omega
        rcases Nat.even_or_odd (k - m) with hev | hod
        · exfalso
          have : Even (m + k) := by rw [hsum]; exact Even.add hev (even_two_mul m)
          exact (Nat.not_even_iff_odd.mpr hodd) this
        · exact hod
      have hnkm : ¬ (p ≠ 0 ∧ q ≠ 0 ∧ k < m ∧ Odd (m - k)) := by
        rintro ⟨_, _, hkm, _⟩
        exact (not_lt.mpr (le_of_lt hmk)) hkm
      rw [if_neg hnkm, if_pos ⟨hq, hp, hmk, hod2⟩, zero_add]

theorem exists_eval_ge_of_degree_pos (p : Polynomial ℝ) (hd : 0 < p.degree) :
    ∀ (B r : ℝ), ∃ M ≥ r, B ≤ p.leadingCoeff * p.eval M := by
  refine Polynomial.degree_pos_induction_on p hd ?_ ?_ ?_
  · intro a ha B r
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    let M := max r (B / a ^ 2)
    refine ⟨M, le_max_left _ _, ?_⟩
    simp only [Polynomial.leadingCoeff_mul_X, Polynomial.leadingCoeff_C,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hBM : B / a ^ 2 ≤ M := le_max_right _ _
    have hmul : a ^ 2 * (B / a ^ 2) ≤ a ^ 2 * M :=
      mul_le_mul_of_nonneg_left hBM (le_of_lt ha2)
    have hcancel : a ^ 2 * (B / a ^ 2) = B := mul_div_cancel₀ B (ne_of_gt ha2)
    linarith [show a * (a * M) = a ^ 2 * M by ring]
  · intro q hq ih B r
    obtain ⟨M, hMr, hMB⟩ := ih (max B 0) (max r 1)
    refine ⟨M, le_trans (le_max_left r 1) hMr, ?_⟩
    simp only [Polynomial.leadingCoeff_mul_X, Polynomial.eval_mul, Polynomial.eval_X]
    have hM1 : 1 ≤ M := le_trans (le_max_right r 1) hMr
    have hq_nonneg : 0 ≤ q.leadingCoeff * q.eval M := le_trans (le_max_right B 0) hMB
    have hB : B ≤ q.leadingCoeff * q.eval M := le_trans (le_max_left B 0) hMB
    nlinarith
  · intro q a hq ih B r
    obtain ⟨M, hMr, hMB⟩ := ih (B - q.leadingCoeff * a) r
    refine ⟨M, hMr, ?_⟩
    have hdeg : (Polynomial.C a).degree < q.degree :=
      Polynomial.degree_C_le.trans_lt hq
    rw [add_comm, Polynomial.leadingCoeff_add_of_degree_lt hdeg]
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    linarith

theorem exists_pos_leadingCoeff_mul_eval (g : Polynomial ℝ) (hg : g ≠ 0) (r : ℝ) :
    ∃ M ≥ r, 0 < g.leadingCoeff * g.eval M := by
  rcases le_or_gt g.degree 0 with hd | hd
  · refine ⟨r, le_refl r, ?_⟩
    rw [Polynomial.eq_C_of_degree_le_zero hd] at hg ⊢
    have hc : g.coeff 0 ≠ 0 := fun h ↦ hg (by simp [h])
    simp only [Polynomial.leadingCoeff_C, Polynomial.eval_C]
    exact mul_self_pos.mpr hc
  · obtain ⟨M, hMr, hM⟩ := exists_eval_ge_of_degree_pos g hd 1 r
    exact ⟨M, hMr, lt_of_lt_of_le zero_lt_one hM⟩

theorem realSign_eval_of_forall_root_lt (g : Polynomial ℝ) (hg : g ≠ 0) (r : ℝ)
    (hroots : ∀ x : ℝ, g.IsRoot x → x < r) :
    realSign (g.eval r) = realSign g.leadingCoeff := by
  obtain ⟨M, hMr, hM⟩ := exists_pos_leadingCoeff_mul_eval g hg r
  have hlc_ne : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg
  have hpos : 0 < g.leadingCoeff * g.eval r := by
    refine lt_of_not_ge (fun hle ↦ ?_)
    have hcont : ContinuousOn (fun x ↦ g.leadingCoeff * g.eval x) (Set.Icc r M) :=
      (continuous_const.mul g.continuous).continuousOn
    have h0_mem : (0 : ℝ) ∈ Set.Icc (g.leadingCoeff * g.eval r) (g.leadingCoeff * g.eval M) :=
      ⟨hle, le_of_lt hM⟩
    obtain ⟨z, ⟨hzr, _⟩, hfz⟩ := intermediate_value_Icc hMr hcont h0_mem
    have hgz : g.IsRoot z := (mul_eq_zero.mp hfz).resolve_left hlc_ne
    exact (not_lt_of_ge hzr) (hroots z hgz)
  have hsq : realSign g.leadingCoeff * realSign g.leadingCoeff = 1 :=
    realSign_sq_of_ne_zero hlc_ne
  have hmul : realSign g.leadingCoeff * realSign (g.eval r) = 1 := by
    rw [← realSign_mul, realSign_pos hpos]
  calc
    realSign (g.eval r) = (realSign g.leadingCoeff * realSign g.leadingCoeff) *
        realSign (g.eval r) := by rw [hsq, one_mul]
    _ = realSign g.leadingCoeff * (realSign g.leadingCoeff * realSign (g.eval r)) := by ring
    _ = realSign g.leadingCoeff := by rw [hmul, mul_one]

theorem realSign_leadingCoeff_eq_minftyCoeff_of_no_roots (f : Polynomial ℝ) (hf : f ≠ 0)
    (hroots : ∀ x : ℝ, ¬ f.IsRoot x) :
    realSign f.leadingCoeff = realSign (minftyCoeff f) := by
  have h1 : realSign (f.eval 0) = realSign f.leadingCoeff :=
    realSign_eval_of_forall_root_lt f hf 0 (fun x hx ↦ False.elim (hroots x hx))
  let fn := f.comp (Polynomial.C (-1 : ℝ) * Polynomial.X)
  have hfn_coeff_gen : ∀ (p : Polynomial ℝ) (i : ℕ),
      (p.comp (Polynomial.C (-1 : ℝ) * Polynomial.X)).coeff i = p.coeff i * (-1 : ℝ) ^ i := by
    intro p
    refine Polynomial.induction_on' p ?_ ?_
    · intro p₁ p₂ h₁ h₂ i
      rw [Polynomial.add_comp, Polynomial.coeff_add, h₁, h₂, Polynomial.coeff_add, add_mul]
    · intro k a i
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
          Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← Polynomial.C_pow,
          ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
          Polynomial.coeff_C_mul_X_pow]
      split_ifs with h
      · subst h; rfl
      · simp
  have hfn_coeff : ∀ i : ℕ, fn.coeff i = f.coeff i * (-1 : ℝ) ^ i := hfn_coeff_gen f
  have hfn_ne : fn ≠ 0 := by
    intro h0
    have hc := hfn_coeff f.natDegree
    rw [h0, Polynomial.coeff_zero, Polynomial.coeff_natDegree] at hc
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf)
      (pow_ne_zero _ (by norm_num)) hc.symm
  have hfn_roots : ∀ x : ℝ, ¬ fn.IsRoot x := by
    intro x hx
    rw [Polynomial.IsRoot, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, neg_one_mul] at hx
    exact hroots (-x) hx
  have h2 : realSign (fn.eval 0) = realSign fn.leadingCoeff :=
    realSign_eval_of_forall_root_lt fn hfn_ne 0 (fun x hx ↦ False.elim (hfn_roots x hx))
  have heval0 : fn.eval 0 = f.eval 0 := by
    simp [fn, Polynomial.eval_comp]
  have hnd : fn.natDegree = f.natDegree := by
    refine le_antisymm ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro i hi
      rw [hfn_coeff i, Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
    · refine Polynomial.le_natDegree_of_ne_zero ?_
      rw [hfn_coeff f.natDegree, Polynomial.coeff_natDegree]
      exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf) (pow_ne_zero _ (by norm_num))
  have hlc_fn : fn.leadingCoeff = minftyCoeff f := by
    rw [minftyCoeff_eq_of_ne_zero f hf, Polynomial.leadingCoeff, hnd,
        hfn_coeff f.natDegree, Polynomial.coeff_natDegree, mul_comm]
  rw [← h1, ← heval0, h2, hlc_fn]

theorem sum_realSign_germ_sub_eq (f : Polynomial ℝ) (hf : f ≠ 0) :
    ∑ x ∈ f.roots.toFinset, (realSign (germRight f x) - realSign (germLeft f x)) =
      realSign f.leadingCoeff - realSign (minftyCoeff f) := by
  induction hn : f.natDegree using Nat.strongRecOn generalizing f with
  | ind n ih =>
    by_cases hne : f.roots.toFinset.Nonempty
    · let r := f.roots.toFinset.max' hne
      have hr_mem : r ∈ f.roots.toFinset := Finset.max'_mem _ hne
      have hr_root : f.IsRoot r := (Polynomial.mem_roots hf).mp (Multiset.mem_toFinset.mp hr_mem)
      let m := f.rootMultiplicity r
      have hm_pos : 0 < m := (Polynomial.rootMultiplicity_pos hf).mpr hr_root
      let g := f /ₘ (Polynomial.X - Polynomial.C r) ^ m
      have hfg : (Polynomial.X - Polynomial.C r) ^ m * g = f :=
        Polynomial.pow_mul_divByMonic_rootMultiplicity_eq f r
      have hmonic : ((Polynomial.X - Polynomial.C r) ^ m).Monic :=
        (Polynomial.monic_X_sub_C r).pow m
      have hg_ne : g ≠ 0 := by
        intro hg0
        rw [hg0, mul_zero] at hfg
        exact hf hfg.symm
      have hgr_ne : g.eval r ≠ 0 :=
        Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero r hf
      have hnd_f : f.natDegree = m + g.natDegree := by
        rw [← hfg, Polynomial.natDegree_mul hmonic.ne_zero hg_ne,
            Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      have hnd_lt : g.natDegree < n := by omega
      have hlc_fg : f.leadingCoeff = g.leadingCoeff := by
        rw [← hfg, Polynomial.leadingCoeff_monic_mul hmonic]
      have hminf_fg : minftyCoeff f = (-1 : ℝ) ^ m * minftyCoeff g := by
        rw [minftyCoeff_eq_of_ne_zero f hf, minftyCoeff_eq_of_ne_zero g hg_ne,
            hnd_f, pow_add, hlc_fg, mul_assoc]
      have hr_not_mem_g : r ∉ g.roots.toFinset := by
        intro hmem
        exact hgr_ne ((Polynomial.mem_roots hg_ne).mp (Multiset.mem_toFinset.mp hmem))
      have hroots_eq : f.roots.toFinset = insert r g.roots.toFinset := by
        ext x
        simp only [Multiset.mem_toFinset, Finset.mem_insert,
          Polynomial.mem_roots hf, Polynomial.mem_roots hg_ne]
        rw [← hfg, Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero,
            pow_eq_zero_iff (ne_of_gt hm_pos), sub_eq_zero]
        rfl
      have hg_roots_lt : ∀ x : ℝ, g.IsRoot x → x < r := by
        intro x hx
        have hx_f : x ∈ f.roots.toFinset := by
          rw [hroots_eq]
          exact Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hg_ne).mpr hx))
        have hx_le : x ≤ r := Finset.le_max' _ x hx_f
        have hx_ne : x ≠ r := fun h ↦ by subst h; exact hgr_ne hx
        exact lt_of_le_of_ne hx_le hx_ne
      have hsign_gr : realSign (g.eval r) = realSign g.leadingCoeff :=
        realSign_eval_of_forall_root_lt g hg_ne r hg_roots_lt
      have hterm_r :
          realSign (germRight f r) - realSign (germLeft f r) =
            (1 - (-1 : ℤ) ^ m) * realSign g.leadingCoeff := by
        have hgr_f : germRight f r = g.eval r := by
          rw [← hfg, germRight_mul, germRight_pow, germRight_X_sub_C_self,
              one_pow, one_mul, germRight_of_eval_ne_zero hgr_ne]
        rw [realSign_germLeft, show f.rootMultiplicity r = m from rfl, hgr_f, hsign_gr]
        ring
      have hterm_other : ∀ x ∈ g.roots.toFinset,
          realSign (germRight f x) - realSign (germLeft f x) =
            (-1 : ℤ) ^ m * (realSign (germRight g x) - realSign (germLeft g x)) := by
        intro x hx
        have hx_root : g.IsRoot x := (Polynomial.mem_roots hg_ne).mp (Multiset.mem_toFinset.mp hx)
        have hxr : x < r := hg_roots_lt x hx_root
        have hpow_eval : ((Polynomial.X - Polynomial.C r) ^ m).eval x = (x - r) ^ m := by
          simp
        have hpow_ne : ((Polynomial.X - Polynomial.C r) ^ m).eval x ≠ 0 := by
          rw [hpow_eval]
          exact pow_ne_zero m (sub_ne_zero.mpr (ne_of_lt hxr))
        have hsign_pow : realSign (((Polynomial.X - Polynomial.C r) ^ m).eval x) = (-1 : ℤ) ^ m := by
          rw [hpow_eval, realSign_pow, realSign_neg (sub_neg.mpr hxr)]
        have hgr_x : realSign (germRight f x) = (-1 : ℤ) ^ m * realSign (germRight g x) := by
          rw [← hfg, germRight_mul, germRight_of_eval_ne_zero hpow_ne, realSign_mul, hsign_pow]
        have hgl_x : realSign (germLeft f x) = (-1 : ℤ) ^ m * realSign (germLeft g x) := by
          rw [← hfg, germLeft_mul hmonic.ne_zero hg_ne, germLeft_of_eval_ne_zero hpow_ne,
              realSign_mul, hsign_pow]
        rw [hgr_x, hgl_x, ← mul_sub]
      have ih_g := ih g.natDegree hnd_lt g hg_ne rfl
      rw [hroots_eq, Finset.sum_insert hr_not_mem_g, hterm_r,
          Finset.sum_congr rfl (fun x hx ↦ hterm_other x hx), ← Finset.mul_sum,
          ih_g, hlc_fg, hminf_fg, realSign_mul, realSign_neg_one_pow]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty]
      have hno_roots : ∀ x : ℝ, ¬ f.IsRoot x := by
        intro x hx
        have : x ∈ f.roots.toFinset :=
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf).mpr hx)
        rw [hne] at this
        simp at this
      rw [realSign_leadingCoeff_eq_minftyCoeff_of_no_roots f hf hno_roots, sub_self]

noncomputable def singleInftyJump (f : Polynomial ℝ) : ℤ :=
  haveI := Classical.propDecidable
  (if minftyCoeff f < 0 then 1 else 0) - (if f.leadingCoeff < 0 then 1 else 0)

theorem two_mul_singleInftyJump {f : Polynomial ℝ} (hf : f ≠ 0) :
    2 * singleInftyJump f = realSign f.leadingCoeff - realSign (minftyCoeff f) :=
  two_mul_ite_neg_sub (minftyCoeff_ne_zero f hf) (Polynomial.leadingCoeff_ne_zero.mpr hf)

theorem sum_singleRootJump_eq_singleInftyJump (f : Polynomial ℝ) (hf : f ≠ 0) :
    ∑ x ∈ f.roots.toFinset, singleRootJump f x = singleInftyJump f := by
  suffices h2 : 2 * (∑ x ∈ f.roots.toFinset, singleRootJump f x) = 2 * singleInftyJump f by
    omega
  rw [Finset.mul_sum,
      Finset.sum_congr rfl (fun x _ ↦ two_mul_singleRootJump hf x),
      two_mul_singleInftyJump hf]
  exact sum_realSign_germ_sub_eq f hf

noncomputable def inftyJump (p q : Polynomial ℝ) : ℤ :=
  haveI := Classical.propDecidable
  (if minftyCoeff p * minftyCoeff q < 0 then 1 else 0) -
    (if p.leadingCoeff * q.leadingCoeff < 0 then 1 else 0)

theorem minftyCoeff_mul {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    minftyCoeff (p * q) = minftyCoeff p * minftyCoeff q := by
  rw [minftyCoeff_eq_of_ne_zero (p * q) (mul_ne_zero hp hq),
      minftyCoeff_eq_of_ne_zero p hp,
      minftyCoeff_eq_of_ne_zero q hq,
      Polynomial.natDegree_mul hp hq, pow_add, Polynomial.leadingCoeff_mul]
  ring

theorem inftyJump_eq_singleInftyJump_mul {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    inftyJump p q = singleInftyJump (p * q) := by
  unfold inftyJump singleInftyJump
  rw [minftyCoeff_mul hp hq, Polynomial.leadingCoeff_mul]

theorem cauchyIndex_add_symm {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    cauchyIndex p q + cauchyIndex q p = inftyJump p q := by
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  have hsub_p : p.roots.toFinset ⊆ (p * q).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.roots_mul hpq, Multiset.mem_add]
    exact Or.inl (Multiset.mem_toFinset.mp hx)
  have hsub_q : q.roots.toFinset ⊆ (p * q).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.roots_mul hpq, Multiset.mem_add]
    exact Or.inr (Multiset.mem_toFinset.mp hx)
  rw [cauchyIndex_eq_sum_of_subset p q (p * q).roots.toFinset hsub_p,
      cauchyIndex_eq_sum_of_subset q p (p * q).roots.toFinset hsub_q,
      ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun x _ ↦ cauchyJump_add_symm hp hq x),
      sum_singleRootJump_eq_singleInftyJump (p * q) hpq,
      inftyJump_eq_singleInftyJump_mul hp hq]

theorem cauchyIndex_step {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    cauchyIndex p q = inftyJump p q + cauchyIndex q (realNextMod p q) := by
  rw [cauchyIndex_realNextMod hp hq, ← cauchyIndex_add_symm hp hq]
  ring

theorem realChangesPoly_realMods_step {p q : Polynomial ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    realChangesPoly (realMods p q) =
      inftyJump p q + realChangesPoly (realMods q (realNextMod p q)) := by
  classical
  rw [realMods_cons p q hp, realMods_cons q (realNextMod p q) hq]
  unfold realChangesPoly realSeqMInfty realSeqPInfty inftyJump
  simp only [List.map, realChanges_cons_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  ring

theorem realChangesPoly_realMods_eq_cauchyIndex (p q : Polynomial ℝ) :
    realChangesPoly (realMods p q) = cauchyIndex p q := by
  induction hs : realSize q using Nat.strongRecOn generalizing p q with
  | ind s ih =>
    by_cases hp : p = 0
    · subst hp
      simp [realMods_zero_left, realChangesPoly, realSeqMInfty, realSeqPInfty]
    · by_cases hq : q = 0
      · subst hq
        rw [realMods_cons p 0 hp, realMods_zero_left]
        simp [realChangesPoly, realSeqMInfty, realSeqPInfty]
      · have hlt : realSize (realNextMod p q) < s := by
          rw [← hs]
          exact realSize_realNextMod_lt p q hq
        rw [realChangesPoly_realMods_step hp hq, cauchyIndex_step hp hq,
            ih (realSize (realNextMod p q)) hlt q (realNextMod p q) rfl]

noncomputable def realTaqR (p q : Polynomial ℝ) : ℤ :=
  realChangesPoly (realMods p (p.derivative * q))

theorem realTaqR_eq_tarskiQueryR (p q : Polynomial ℝ) :
    realTaqR p q = tarskiQueryR p q := by
  rw [realTaqR, realChangesPoly_realMods_eq_cauchyIndex, cauchyIndex_derivative_mul]

theorem realTaqR_one (p : Polynomial ℝ) :
    realTaqR p 1 = (p.roots.toFinset.card : ℤ) := by
  rw [realTaqR_eq_tarskiQueryR, tarskiQueryR]
  simp [Polynomial.eval_one, realSign_one]

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

open Grunbaum2003.FormulaCompiler

abbrev CodeItem := Bool × Code

def defaultCodeItem : CodeItem := (false, [])

def itemCode : Item → CodeItem
  | .inl t => (false, t.code)
  | .inr p => (true, p.code)

def stepBinaryCode (b1 b2 bout : Bool) (tag : ℕ) (s : List CodeItem) : Option (List CodeItem) :=
  if 2 ≤ s.length ∧ (s.getD 0 defaultCodeItem).1 = b2 ∧ (s.getD 1 defaultCodeItem).1 = b1 then
    some ((bout, (s.getD 1 defaultCodeItem).2 ++ (s.getD 0 defaultCodeItem).2 ++ [(tag, 0)]) :: s.drop 2)
  else none

def stepUnaryCode (bin bout : Bool) (tag : ℕ) (s : List CodeItem) : Option (List CodeItem) :=
  if 1 ≤ s.length ∧ (s.getD 0 defaultCodeItem).1 = bin then
    some ((bout, (s.getD 0 defaultCodeItem).2 ++ [(tag, 0)]) :: s.drop 1)
  else none

theorem primrec_stepBinaryCode (b1 b2 bout : Bool) (tag : ℕ) :
    Primrec (stepBinaryCode b1 b2 bout tag) := by
  have he0 : Primrec (fun s : List CodeItem => s.getD 0 defaultCodeItem) :=
    (Primrec.list_getD defaultCodeItem).comp Primrec.id (Primrec.const 0)
  have he1 : Primrec (fun s : List CodeItem => s.getD 1 defaultCodeItem) :=
    (Primrec.list_getD defaultCodeItem).comp Primrec.id (Primrec.const 1)
  have hcond : PrimrecPred (fun s : List CodeItem =>
      2 ≤ s.length ∧ (s.getD 0 defaultCodeItem).1 = b2 ∧ (s.getD 1 defaultCodeItem).1 = b1) :=
    PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 2) Primrec.list_length)
      (PrimrecPred.and (Primrec.eq.comp (Primrec.fst.comp he0) (Primrec.const b2))
        (Primrec.eq.comp (Primrec.fst.comp he1) (Primrec.const b1)))
  have hcode : Primrec (fun s : List CodeItem =>
      (s.getD 1 defaultCodeItem).2 ++ (s.getD 0 defaultCodeItem).2 ++ [(tag, 0)]) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.snd.comp he1) (Primrec.snd.comp he0))
      (Primrec.const [(tag, 0)])
  have hcons : Primrec (fun s : List CodeItem =>
      (bout, (s.getD 1 defaultCodeItem).2 ++ (s.getD 0 defaultCodeItem).2 ++ [(tag, 0)]) :: s.drop 2) :=
    Primrec.list_cons.comp ((Primrec.const bout).pair hcode)
      (Primrec.list_drop.comp (Primrec.const 2) Primrec.id)
  exact Primrec.ite hcond (Primrec.option_some.comp hcons) (Primrec.const none)

theorem primrec_stepUnaryCode (bin bout : Bool) (tag : ℕ) :
    Primrec (stepUnaryCode bin bout tag) := by
  have he0 : Primrec (fun s : List CodeItem => s.getD 0 defaultCodeItem) :=
    (Primrec.list_getD defaultCodeItem).comp Primrec.id (Primrec.const 0)
  have hcond : PrimrecPred (fun s : List CodeItem =>
      1 ≤ s.length ∧ (s.getD 0 defaultCodeItem).1 = bin) :=
    PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 1) Primrec.list_length)
      (Primrec.eq.comp (Primrec.fst.comp he0) (Primrec.const bin))
  have hcode : Primrec (fun s : List CodeItem =>
      (s.getD 0 defaultCodeItem).2 ++ [(tag, 0)]) :=
    Primrec.list_append.comp (Primrec.snd.comp he0) (Primrec.const [(tag, 0)])
  have hcons : Primrec (fun s : List CodeItem =>
      (bout, (s.getD 0 defaultCodeItem).2 ++ [(tag, 0)]) :: s.drop 1) :=
    Primrec.list_cons.comp ((Primrec.const bout).pair hcode)
      (Primrec.list_drop.comp (Primrec.const 1) Primrec.id)
  exact Primrec.ite hcond (Primrec.option_some.comp hcons) (Primrec.const none)

def stepCode (tok : Token) (s : List CodeItem) : Option (List CodeItem) :=
  if tok.1 = 0 then some ((false, [(0, tok.2)]) :: s)
  else if tok.1 = 1 then some ((false, [(1, 0)]) :: s)
  else if tok.1 = 2 then some ((false, [(2, 0)]) :: s)
  else if tok.1 = 3 then stepBinaryCode false false false 3 s
  else if tok.1 = 4 then stepBinaryCode false false false 4 s
  else if tok.1 = 5 then stepUnaryCode false false 5 s
  else if tok.1 = 6 then some ((true, [(6, if tok.2 = 1 then 1 else 0)]) :: s)
  else if tok.1 = 7 then stepBinaryCode false false true 7 s
  else if tok.1 = 8 then stepBinaryCode false false true 8 s
  else if tok.1 = 9 then stepBinaryCode false false true 9 s
  else if tok.1 = 10 then stepUnaryCode true true 10 s
  else if tok.1 = 11 then stepBinaryCode true true true 11 s
  else if tok.1 = 12 then stepBinaryCode true true true 12 s
  else if tok.1 = 13 then stepUnaryCode true true 13 s
  else if tok.1 = 14 then stepUnaryCode true true 14 s
  else none

theorem primrec_stepCode : Primrec₂ stepCode := by
  have htag : Primrec (fun z : Token × List CodeItem => z.1.1) := Primrec.fst.comp Primrec.fst
  have hval : Primrec (fun z : Token × List CodeItem => z.1.2) := Primrec.snd.comp Primrec.fst
  have hs : Primrec (fun z : Token × List CodeItem => z.2) := Primrec.snd
  have h0 : Primrec (fun z : Token × List CodeItem => some ((false, [(0, z.1.2)]) :: z.2)) :=
    Primrec.option_some.comp (Primrec.list_cons.comp
      ((Primrec.const false).pair (Primrec.list_cons.comp ((Primrec.const 0).pair hval) (Primrec.const []))) hs)
  have h1 : Primrec (fun z : Token × List CodeItem => some ((false, [(1, 0)]) :: z.2)) :=
    Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.const (false, [(1, 0)])) hs)
  have h2 : Primrec (fun z : Token × List CodeItem => some ((false, [(2, 0)]) :: z.2)) :=
    Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.const (false, [(2, 0)])) hs)
  have h6 : Primrec (fun z : Token × List CodeItem =>
      some ((true, [(6, if z.1.2 = 1 then 1 else 0)]) :: z.2)) :=
    Primrec.option_some.comp (Primrec.list_cons.comp
      ((Primrec.const true).pair (Primrec.list_cons.comp
        ((Primrec.const 6).pair (Primrec.ite (Primrec.eq.comp hval (Primrec.const 1))
          (Primrec.const 1) (Primrec.const 0))) (Primrec.const []))) hs)
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) h0
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) h1
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) h2
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) ((primrec_stepBinaryCode false false false 3).comp hs)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) ((primrec_stepBinaryCode false false false 4).comp hs)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) ((primrec_stepUnaryCode false false 5).comp hs)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) h6
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 7)) ((primrec_stepBinaryCode false false true 7).comp hs)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 8)) ((primrec_stepBinaryCode false false true 8).comp hs)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 9)) ((primrec_stepBinaryCode false false true 9).comp hs)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 10)) ((primrec_stepUnaryCode true true 10).comp hs)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 11)) ((primrec_stepBinaryCode true true true 11).comp hs)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 12)) ((primrec_stepBinaryCode true true true 12).comp hs)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 13)) ((primrec_stepUnaryCode true true 13).comp hs)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 14)) ((primrec_stepUnaryCode true true 14).comp hs)
      (Primrec.const none)))))))))))))))

def runCode (c : Code) (s : Option (List CodeItem)) : Option (List CodeItem) :=
  c.foldl (fun s t => s.bind (stepCode t)) s

theorem primrec_runCode : Primrec₂ runCode :=
  Primrec.list_foldl Primrec.fst Primrec.snd
    (Primrec.option_bind (Primrec.fst.comp Primrec.snd)
      (primrec_stepCode.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂).to₂

theorem stepCode_map_itemCode (tok : Token) (s : List Item) :
    stepCode tok (s.map itemCode) = (step tok s).map (List.map itemCode) := by
  rcases tok with ⟨tag, val⟩
  match tag with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases s1 with
      | nil => cases x1 <;> rfl
      | cons x2 s2 =>
        cases x1 <;> cases x2 <;> rfl
  | 4 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases s1 with
      | nil => cases x1 <;> rfl
      | cons x2 s2 =>
        cases x1 <;> cases x2 <;> rfl
  | 5 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases x1 <;> rfl
  | 6 =>
    simp only [stepCode, step]
    by_cases h : val = 1 <;> simp [h, itemCode, Formula.code]
  | 7 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases s1 with
      | nil => cases x1 <;> rfl
      | cons x2 s2 =>
        cases x1 <;> cases x2 <;> rfl
  | 8 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases s1 with
      | nil => cases x1 <;> rfl
      | cons x2 s2 =>
        cases x1 <;> cases x2 <;> rfl
  | 9 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases s1 with
      | nil => cases x1 <;> rfl
      | cons x2 s2 =>
        cases x1 <;> cases x2 <;> rfl
  | 10 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases x1 <;> rfl
  | 11 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases s1 with
      | nil => cases x1 <;> rfl
      | cons x2 s2 =>
        cases x1 <;> cases x2 <;> rfl
  | 12 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases s1 with
      | nil => cases x1 <;> rfl
      | cons x2 s2 =>
        cases x1 <;> cases x2 <;> rfl
  | 13 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases x1 <;> rfl
  | 14 =>
    cases s with
    | nil => rfl
    | cons x1 s1 =>
      cases x1 <;> rfl
  | n + 15 =>
    simp [stepCode, step]

theorem runCode_map_itemCode (c : Code) (s : Option (List Item)) :
    runCode c (s.map (List.map itemCode)) = (run c s).map (List.map itemCode) := by
  induction c generalizing s with
  | nil => rfl
  | cons tok c ih =>
    simp only [runCode, run, List.foldl_cons]
    have hs : (s.map (List.map itemCode)).bind (stepCode tok) =
        (s.bind (step tok)).map (List.map itemCode) := by
      cases s with
      | none => rfl
      | some xs => exact stepCode_map_itemCode tok xs
    rw [hs]
    exact ih (s.bind (step tok))

def decodeTerm (c : Code) : Option Term :=
  match run c (some []) with
  | some [.inl t] => some t
  | _ => none

@[simp] theorem decodeTerm_code (t : Term) : decodeTerm t.code = some t := by
  simp only [decodeTerm, run_term_code]

def normalizeCode (b : Bool) (c : Code) : Option Code :=
  (runCode c (some [])).bind (fun xs =>
    if xs.length = 1 ∧ (xs.getD 0 defaultCodeItem).1 = b then
      some (xs.getD 0 defaultCodeItem).2
    else none)

theorem primrec_normalizeCode (b : Bool) : Primrec (normalizeCode b) := by
  refine Primrec.option_bind (primrec_runCode.comp Primrec.id (Primrec.const (some []))) ?_
  have he0 : Primrec (fun z : Code × List CodeItem => z.2.getD 0 defaultCodeItem) :=
    (Primrec.list_getD defaultCodeItem).comp Primrec.snd (Primrec.const 0)
  have hcond : PrimrecPred (fun z : Code × List CodeItem =>
      z.2.length = 1 ∧ (z.2.getD 0 defaultCodeItem).1 = b) :=
    PrimrecPred.and (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1))
      (Primrec.eq.comp (Primrec.fst.comp he0) (Primrec.const b))
  exact (Primrec.ite hcond (Primrec.option_some.comp (Primrec.snd.comp he0)) (Primrec.const none)).to₂

theorem normalizeCode_false_eq (c : Code) :
    normalizeCode false c = (decodeTerm c).map Term.code := by
  unfold normalizeCode decodeTerm
  have h := runCode_map_itemCode c (some [])
  simp only [Option.map_some, List.map_nil] at h
  rw [h]
  cases hrun : run c (some []) with
  | none => rfl
  | some xs =>
    cases xs with
    | nil => rfl
    | cons x rest =>
      cases rest with
      | nil =>
        cases x <;> rfl
      | cons y rest' =>
        simp

theorem normalizeCode_true_eq (c : Code) :
    normalizeCode true c = (decode c).map Formula.code := by
  unfold normalizeCode decode
  have h := runCode_map_itemCode c (some [])
  simp only [Option.map_some, List.map_nil] at h
  rw [h]
  cases hrun : run c (some []) with
  | none => rfl
  | some xs =>
    cases xs with
    | nil => rfl
    | cons x rest =>
      cases rest with
      | nil =>
        cases x <;> rfl
      | cons y rest' =>
        simp

instance instEncodableTerm : Encodable Term where
  encode t := Encodable.encode t.code
  decode n := (Encodable.decode (α := Code) n).bind decodeTerm
  encodek t := by simp

instance instEncodableFormula : Encodable Formula where
  encode p := Encodable.encode p.code
  decode n := (Encodable.decode (α := Code) n).bind decode
  encodek p := by simp

theorem encode_option_term (o : Option Term) :
    Encodable.encode o = Encodable.encode (o.map Term.code) := by
  cases o <;> rfl

theorem encode_option_formula (o : Option Formula) :
    Encodable.encode o = Encodable.encode (o.map Formula.code) := by
  cases o <;> rfl

instance instPrimcodableTerm : Primcodable Term where
  prim := by
    have h : Primrec (fun n : ℕ =>
        Encodable.encode ((Encodable.decode (α := Code) n).bind (normalizeCode false))) :=
      Primrec.encode.comp (Primrec.option_bind Primrec.decode
        ((primrec_normalizeCode false).comp Primrec.snd).to₂)
    refine Primrec.nat_iff.mp (h.of_eq (fun n => ?_))
    rw [encode_option_term]
    change Encodable.encode ((Encodable.decode (α := Code) n).bind (normalizeCode false)) =
      Encodable.encode (((Encodable.decode (α := Code) n).bind decodeTerm).map Term.code)
    congr 1
    cases Encodable.decode (α := Code) n with
    | none => rfl
    | some c => exact normalizeCode_false_eq c

instance instPrimcodableFormula : Primcodable Formula where
  prim := by
    have h : Primrec (fun n : ℕ =>
        Encodable.encode ((Encodable.decode (α := Code) n).bind (normalizeCode true))) :=
      Primrec.encode.comp (Primrec.option_bind Primrec.decode
        ((primrec_normalizeCode true).comp Primrec.snd).to₂)
    refine Primrec.nat_iff.mp (h.of_eq (fun n => ?_))
    rw [encode_option_formula]
    change Encodable.encode ((Encodable.decode (α := Code) n).bind (normalizeCode true)) =
      Encodable.encode (((Encodable.decode (α := Code) n).bind decode).map Formula.code)
    congr 1
    cases Encodable.decode (α := Code) n with
    | none => rfl
    | some c => exact normalizeCode_true_eq c

theorem primrec_term_code : Primrec Term.code := by
  rw [Primrec]
  simpa only [← encode_option_term] using Primcodable.prim (α := Term)

theorem primrec_formula_code : Primrec Formula.code := by
  rw [Primrec]
  simpa only [← encode_option_formula] using Primcodable.prim (α := Formula)

theorem primrec_decodeTerm : Primrec decodeTerm := by
  rw [Primrec]
  have h : Primrec (fun n : ℕ =>
      Encodable.encode ((Encodable.decode (α := Code) n).map (normalizeCode false))) :=
    Primrec.encode.comp (Primrec.option_map Primrec.decode
      ((primrec_normalizeCode false).comp Primrec.snd).to₂)
  refine Primrec.nat_iff.mp (h.of_eq (fun n => ?_))
  cases Encodable.decode (α := Code) n with
  | none => rfl
  | some c =>
    simp only [Option.map_some, Encodable.encode_some, normalizeCode_false_eq, encode_option_term]

theorem primrec_decode : Primrec decode := by
  rw [Primrec]
  have h : Primrec (fun n : ℕ =>
      Encodable.encode ((Encodable.decode (α := Code) n).map (normalizeCode true))) :=
    Primrec.encode.comp (Primrec.option_map Primrec.decode
      ((primrec_normalizeCode true).comp Primrec.snd).to₂)
  refine Primrec.nat_iff.mp (h.of_eq (fun n => ?_))
  cases Encodable.decode (α := Code) n with
  | none => rfl
  | some c =>
    simp only [Option.map_some, Encodable.encode_some, normalizeCode_true_eq, encode_option_formula]

theorem primrec_of_term_code {A : Type*} [Primcodable A] {f : A → Term}
    (hf : Primrec (fun a => (f a).code)) : Primrec f :=
  ((Primrec.option_getD.comp (primrec_decodeTerm.comp hf) (Primrec.const .zero))).of_eq
    (fun a => by simp [decodeTerm_code])

theorem computable_of_term_code {A : Type*} [Primcodable A] {f : A → Term}
    (hf : Computable (fun a => (f a).code)) : Computable f :=
  ((Primrec.option_getD.to_comp.comp (primrec_decodeTerm.to_comp.comp hf)
    (Computable.const .zero))).of_eq (fun a => by simp [decodeTerm_code])

theorem primrec_of_formula_code {A : Type*} [Primcodable A] {f : A → Formula}
    (hf : Primrec (fun a => (f a).code)) : Primrec f :=
  ((Primrec.option_getD.comp (primrec_decode.comp hf) (Primrec.const (.truth false)))).of_eq
    (fun a => by simp [decode_code])

theorem computable_of_formula_code {A : Type*} [Primcodable A] {f : A → Formula}
    (hf : Computable (fun a => (f a).code)) : Computable f :=
  ((Primrec.option_getD.to_comp.comp (primrec_decode.to_comp.comp hf)
    (Computable.const (.truth false)))).of_eq (fun a => by simp [decode_code])

def decodePolyCode (pc : PolyCode) : TermPoly :=
  pc.map (fun c => (decodeTerm c).getD .zero)

theorem primrec_decodePolyCode : Primrec decodePolyCode :=
  Primrec.list_map Primrec.id
    ((Primrec.option_getD.comp (primrec_decodeTerm.comp Primrec.snd) (Primrec.const .zero))).to₂

theorem primrec_map_term_code : Primrec (fun p : TermPoly => p.map Term.code) :=
  Primrec.list_map Primrec.id (primrec_term_code.comp Primrec.snd).to₂

@[simp] theorem decodePolyCode_map (p : TermPoly) :
    decodePolyCode (p.map Term.code) = p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons, decodePolyCode, decodeTerm_code, Option.getD_some]
    exact congrArg (List.cons a) ih

theorem primrec_of_poly_code {A : Type*} [Primcodable A] {f : A → TermPoly}
    (hf : Primrec (fun a => (f a).map Term.code)) : Primrec f :=
  (primrec_decodePolyCode.comp hf).of_eq (fun a => decodePolyCode_map (f a))

theorem computable_of_poly_code {A : Type*} [Primcodable A] {f : A → TermPoly}
    (hf : Computable (fun a => (f a).map Term.code)) : Computable f :=
  (primrec_decodePolyCode.to_comp.comp hf).of_eq (fun a => decodePolyCode_map (f a))

theorem primrec_term_var : Primrec Term.var :=
  primrec_of_term_code (primrec_var_code Primrec.id)

theorem primrec_term_add : Primrec₂ Term.add :=
  primrec_of_term_code (primrec_term_add_code
    (primrec_term_code.comp Primrec.fst) (primrec_term_code.comp Primrec.snd))

theorem primrec_term_mul : Primrec₂ Term.mul :=
  primrec_of_term_code (primrec_term_mul_code
    (primrec_term_code.comp Primrec.fst) (primrec_term_code.comp Primrec.snd))

theorem primrec_term_neg : Primrec Term.neg :=
  primrec_of_term_code (primrec_term_neg_code primrec_term_code)

theorem primrec_formula_truth : Primrec Formula.truth :=
  primrec_of_formula_code (primrec_truth_code Primrec.id)

theorem primrec_formula_eq : Primrec₂ Formula.eq :=
  primrec_of_formula_code (primrec_eq_code
    (primrec_term_code.comp Primrec.fst) (primrec_term_code.comp Primrec.snd))

theorem primrec_formula_lt : Primrec₂ Formula.lt :=
  primrec_of_formula_code (primrec_lt_code
    (primrec_term_code.comp Primrec.fst) (primrec_term_code.comp Primrec.snd))

theorem primrec_formula_le : Primrec₂ Formula.le :=
  primrec_of_formula_code (primrec_le_code
    (primrec_term_code.comp Primrec.fst) (primrec_term_code.comp Primrec.snd))

theorem primrec_formula_not : Primrec Formula.not :=
  primrec_of_formula_code (primrec_not_code primrec_formula_code)

theorem primrec_formula_and : Primrec₂ Formula.and :=
  primrec_of_formula_code (primrec_and_code
    (primrec_formula_code.comp Primrec.fst) (primrec_formula_code.comp Primrec.snd))

theorem primrec_formula_or : Primrec₂ Formula.or :=
  primrec_of_formula_code (primrec_or_code
    (primrec_formula_code.comp Primrec.fst) (primrec_formula_code.comp Primrec.snd))

theorem primrec_formula_all : Primrec Formula.all :=
  primrec_of_formula_code (primrec_all_code primrec_formula_code)

theorem primrec_formula_ex : Primrec Formula.ex :=
  primrec_of_formula_code (primrec_ex_code primrec_formula_code)

theorem primrec_formula_imp : Primrec₂ imp :=
  primrec_of_formula_code (primrec_imp_code
    (primrec_formula_code.comp Primrec.fst) (primrec_formula_code.comp Primrec.snd))

theorem primrec_formula_iff : Primrec₂ iffFormula :=
  primrec_of_formula_code (primrec_iff_code
    (primrec_formula_code.comp Primrec.fst) (primrec_formula_code.comp Primrec.snd))

theorem primrec_poly_add : Primrec₂ add :=
  primrec_of_poly_code ((primrec_addCodes.comp
    (primrec_map_term_code.comp Primrec.fst)
    (primrec_map_term_code.comp Primrec.snd)).of_eq (fun z => addCodes_map z.1 z.2))

theorem primrec_poly_scale : Primrec₂ scale :=
  primrec_of_poly_code ((primrec_scaleCodes.comp
    (primrec_term_code.comp Primrec.fst)
    (primrec_map_term_code.comp Primrec.snd)).of_eq (fun z => scaleCodes_map z.1 z.2))

theorem primrec_poly_neg : Primrec neg :=
  primrec_of_poly_code ((primrec_negCodes.comp primrec_map_term_code).of_eq negCodes_map)

theorem primrec_poly_mul : Primrec₂ mul :=
  primrec_of_poly_code ((primrec_mulCodes.comp
    (primrec_map_term_code.comp Primrec.fst)
    (primrec_map_term_code.comp Primrec.snd)).of_eq (fun z => mulCodes_map z.1 z.2))

theorem primrec_poly_shift : Primrec₂ shift :=
  primrec_of_poly_code ((primrec_shiftCodes.comp
    Primrec.fst (primrec_map_term_code.comp Primrec.snd)).of_eq (fun z => shiftCodes_map z.1 z.2))

theorem primrec_poly_termMonomial : Primrec₂ termMonomial :=
  primrec_of_poly_code ((primrec_termMonomialCodes.comp
    Primrec.fst (primrec_term_code.comp Primrec.snd)).of_eq (fun z => termMonomialCodes_map z.1 z.2))

theorem primrec_abstract0 : Primrec abstract0 :=
  primrec_of_poly_code (primrec_abstract0_code primrec_term_code)

theorem primrec_coefficient : Primrec₂ coefficient :=
  (Primrec.list_getD Term.zero).comp Primrec.fst Primrec.snd

theorem primrec_sizeCases {A : Type*} [Primcodable A]
    {p : A → TermPoly} {k : A → ℕ → Formula}
    (hp : Primrec p) (hk : Primrec (fun z : A × ℕ => k z.1 z.2)) :
    Primrec (fun a => sizeCases (p a) (k a)) :=
  primrec_of_formula_code (primrec_sizeCases_code
    (primrec_map_term_code.comp hp) (primrec_formula_code.comp hk))

theorem computable_sizeCases {A : Type*} [Primcodable A]
    {p : A → TermPoly} {k : A → ℕ → Formula}
    (hp : Computable p) (hk : Computable (fun z : A × ℕ => k z.1 z.2)) :
    Computable (fun a => sizeCases (p a) (k a)) := by
  apply computable_of_formula_code
  have hpCode : Computable (fun a => (p a).map Term.code) :=
    primrec_map_term_code.to_comp.comp hp
  have hkCode : Computable (fun z : A × ℕ => (k z.1 z.2).code) :=
    primrec_formula_code.to_comp.comp hk
  exact (computable_sizeTableCode_range (p := fun a => (p a).map Term.code)
    (k := fun a i => (k a i).code) hpCode hkCode).of_eq
    (fun a => by rw [List.length_map]; exact sizeTableCode_eq (p a) (k a))

theorem primrec_leadingCases {A : Type*} [Primcodable A]
    {p : A → TermPoly} {k : A → Term → Formula}
    (hp : Primrec p) (hk : Primrec (fun z : A × Term => k z.1 z.2)) :
    Primrec (fun a => leadingCases (p a) (k a)) := by
  refine primrec_sizeCases hp ?_
  have hterm : Primrec (fun z : A × ℕ =>
      if z.2 = 0 then Term.zero else coefficient (p z.1) (z.2 - 1)) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (Primrec.const Term.zero)
      (primrec_coefficient.comp (hp.comp Primrec.fst)
        (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
  exact hk.comp (Primrec.fst.pair hterm)

theorem computable_leadingCases {A : Type*} [Primcodable A]
    {p : A → TermPoly} {k : A → Term → Formula}
    (hp : Computable p) (hk : Computable (fun z : A × Term => k z.1 z.2)) :
    Computable (fun a => leadingCases (p a) (k a)) := by
  refine computable_sizeCases hp ?_
  have hterm : Computable (fun z : A × ℕ =>
      if z.2 = 0 then Term.zero else coefficient (p z.1) (z.2 - 1)) :=
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (Primrec.const Term.zero)
      (primrec_coefficient.comp Primrec.fst
        (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))).to_comp.comp
      ((hp.comp Computable.fst).pair Computable.snd)
  exact hk.comp (Computable.fst.pair hterm)

theorem computable_pseudoDivCases {A : Type*} [Primcodable A]
    {p q : A → TermPoly}
    {k : A → ℕ → TermPoly → TermPoly → Formula}
    (hp : Computable p) (hq : Computable q)
    (hk : Computable (fun z : A × ℕ × TermPoly × TermPoly => k z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Computable (fun x => pseudoDivCases (p x) (q x) (k x)) := by
  apply computable_of_formula_code
  let kCode : A → ℕ → PolyCode → PolyCode → Code :=
    fun x c a r => (k x c (decodePolyCode a) (decodePolyCode r)).code
  have hkCode : Computable (fun z : A × ℕ × PolyCode × PolyCode =>
      kCode z.1 z.2.1 z.2.2.1 z.2.2.2) := by
    have hargs : Computable (fun z : A × ℕ × PolyCode × PolyCode =>
        (z.1, z.2.1, decodePolyCode z.2.2.1, decodePolyCode z.2.2.2)) :=
      Computable.fst.pair
        ((Computable.fst.comp Computable.snd).pair
          ((primrec_decodePolyCode.to_comp.comp
            (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair
            (primrec_decodePolyCode.to_comp.comp
              (Computable.snd.comp (Computable.snd.comp Computable.snd)))))
    exact primrec_formula_code.to_comp.comp (hk.comp hargs)
  refine computable_pseudoDivCases_code
    (primrec_map_term_code.to_comp.comp hp)
    (primrec_map_term_code.to_comp.comp hq)
    hkCode (fun x c a r => ?_)
  simp only [kCode, decodePolyCode_map]

def evalFormulaAt {S : Type*} [Primcodable S] (c : Nat.Partrec.Code) (s : S) : Part Formula :=
  (evalCodeAt c s).map (fun code => (decode code).getD (.truth false))

theorem partrec_evalFormulaAt {S : Type*} [Primcodable S] :
    Partrec₂ (@evalFormulaAt S _) := by
  refine ((Partrec.map (partrec_evalCodeAt (S := S))
    (((Primrec.option_getD.comp primrec_decode (Primrec.const (.truth false))).to_comp.comp
      Computable.snd).to₂)).of_eq (fun _ => rfl)).to₂

theorem computable_of_decreasing_step_formula {S : Type*} [Primcodable S]
    (F : S → Formula) (fuel : S → ℕ)
    (stepBody : (S → Part Formula) → S → Part Formula)
    (hbody : Partrec₂ (fun c (s : S) => stepBody (evalFormulaAt c) s))
    (hstep : ∀ (recCall : S → Part Formula) (s : S),
      (∀ s', fuel s' < fuel s → recCall s' = Part.some (F s')) →
      stepBody recCall s = Part.some (F s)) :
    Computable F := by
  apply computable_of_formula_code
  let FCode : S → Code := fun s => (F s).code
  let stepBodyCode : (S → Part Code) → S → Part Code :=
    fun recCode s =>
      (stepBody (fun s' => (recCode s').map (fun c => (decode c).getD (.truth false))) s).map
        Formula.code
  have hbodyCode : Partrec₂ (fun c (s : S) => stepBodyCode (evalCodeAt c) s) :=
    (Partrec.map hbody ((primrec_formula_code.to_comp.comp Computable.snd).to₂)).to₂
  refine computable_of_decreasing_step FCode fuel stepBodyCode hbodyCode ?_
  intro recCode s ih
  have hrec : ∀ s', fuel s' < fuel s →
      (recCode s').map (fun c => (decode c).getD (.truth false)) = Part.some (F s') := by
    intro s' hlt
    rw [ih s' hlt, Part.map_some]
    simp only [FCode, decode_code, Option.getD_some]
  simp only [stepBodyCode, hstep _ s hrec, Part.map_some, FCode]

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

open Grunbaum2003.FormulaCompiler

private def foldlStep {A α β : Type*} (step : A → β → α → β)
    (s : A × List α × β) : Part (β ⊕ (A × List α × β)) :=
  s.2.1.head?.casesOn (Part.some (Sum.inl s.2.2))
    (fun x => Part.some (Sum.inr (s.1, s.2.1.tail, step s.1 s.2.2 x)))

set_option backward.isDefEq.respectTransparency false in
private theorem foldlStep_fix_nil {A α β : Type*} (step : A → β → α → β)
    (a : A) (acc : β) :
    PFun.fix (foldlStep step) (a, [], acc) = Part.some acc := by
  apply Part.ext
  intro y
  rw [PFun.mem_fix_iff]
  simp [foldlStep]

set_option backward.isDefEq.respectTransparency false in
private theorem foldlStep_fix_cons {A α β : Type*} (step : A → β → α → β)
    (a : A) (x : α) (xs : List α) (acc : β) :
    PFun.fix (foldlStep step) (a, x :: xs, acc) =
      PFun.fix (foldlStep step) (a, xs, step a acc x) := by
  apply Part.ext
  intro y
  rw [PFun.mem_fix_iff]
  simp [foldlStep]

private theorem foldlStep_fix_eq {A α β : Type*} (step : A → β → α → β)
    (a : A) (xs : List α) (acc : β) :
    PFun.fix (foldlStep step) (a, xs, acc) = Part.some (xs.foldl (step a) acc) := by
  induction xs generalizing acc with
  | nil => exact foldlStep_fix_nil step a acc
  | cons x xs ih =>
    rw [foldlStep_fix_cons, List.foldl_cons, ih]

theorem computable_list_foldl {A α β : Type*}
    [Primcodable A] [Primcodable α] [Primcodable β]
    {l : A → List α} {init : A → β} {step : A → β → α → β}
    (hl : Computable l) (hinit : Computable init)
    (hstep : Computable (fun z : A × β × α => step z.1 z.2.1 z.2.2)) :
    Computable (fun a => (l a).foldl (step a) (init a)) := by
  have hFixStep : Partrec (foldlStep step) := by
    apply Partrec.optionCasesOn_right
      (Primrec.list_head?.to_comp.comp (Computable.fst.comp Computable.snd))
      (Computable.sumInl.comp (Computable.snd.comp Computable.snd))
    have hNext : Computable (fun p : (A × List α × β) × α =>
        Sum.inr (α := β) (p.1.1, p.1.2.1.tail, step p.1.1 p.1.2.2 p.2)) := by
      have ha : Computable (fun p : (A × List α × β) × α => p.1.1) :=
        Computable.fst.comp Computable.fst
      have hxs : Computable (fun p : (A × List α × β) × α => p.1.2.1.tail) :=
        Primrec.list_tail.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
      have hacc : Computable (fun p : (A × List α × β) × α => p.1.2.2) :=
        Computable.snd.comp (Computable.snd.comp Computable.fst)
      have hx : Computable (fun p : (A × List α × β) × α => p.2) := Computable.snd
      have hst : Computable (fun p : (A × List α × β) × α => step p.1.1 p.1.2.2 p.2) :=
        hstep.comp (ha.pair (hacc.pair hx))
      exact Computable.sumInr.comp (ha.pair (hxs.pair hst))
    exact hNext.partrec.to₂
  have hInitState : Computable (fun a : A => (a, l a, init a)) :=
    Computable.id.pair (hl.pair hinit)
  exact ((Partrec.fix hFixStep).comp hInitState).of_eq (fun a => foldlStep_fix_eq step a (l a) (init a))

structure FormulaRecSpec (A F : Type*) where
  defaultF : F
  fTruth : A → Bool → F
  fEq : A → Term → Term → F
  fLt : A → Term → Term → F
  fLe : A → Term → Term → F
  fNot : A → F → F
  fAnd : A → F → F → F
  fOr : A → F → F → F
  fAll : A → F → F
  fEx : A → F → F

def evalFormulaRec {A F : Type*} (spec : FormulaRecSpec A F) (a : A) : Formula → F
  | .truth b => spec.fTruth a b
  | .eq t1 t2 => spec.fEq a t1 t2
  | .lt t1 t2 => spec.fLt a t1 t2
  | .le t1 t2 => spec.fLe a t1 t2
  | .not p => spec.fNot a (evalFormulaRec spec a p)
  | .and p q => spec.fAnd a (evalFormulaRec spec a p) (evalFormulaRec spec a q)
  | .or p q => spec.fOr a (evalFormulaRec spec a p) (evalFormulaRec spec a q)
  | .all p => spec.fAll a (evalFormulaRec spec a p)
  | .ex p => spec.fEx a (evalFormulaRec spec a p)

abbrev RecStackItem (F : Type*) := Term × Bool × F

def defaultRecItem {A F : Type*} (spec : FormulaRecSpec A F) : RecStackItem F :=
  (.zero, false, spec.defaultF)

def stepFormulaRec {A F : Type*} (spec : FormulaRecSpec A F) (a : A)
    (s : List (RecStackItem F)) (tok : Token) : List (RecStackItem F) :=
  let d := defaultRecItem spec
  let e0 := s.getD 0 d
  let e1 := s.getD 1 d
  if tok.1 = 0 then (.var tok.2, false, spec.defaultF) :: s
  else if tok.1 = 1 then (.zero, false, spec.defaultF) :: s
  else if tok.1 = 2 then (.one, false, spec.defaultF) :: s
  else if tok.1 = 3 then (.add e1.1 e0.1, false, spec.defaultF) :: s.drop 2
  else if tok.1 = 4 then (.mul e1.1 e0.1, false, spec.defaultF) :: s.drop 2
  else if tok.1 = 5 then (.neg e0.1, false, spec.defaultF) :: s.drop 1
  else if tok.1 = 6 then (.zero, true, spec.fTruth a (tok.2 == 1)) :: s
  else if tok.1 = 7 then (.zero, true, spec.fEq a e1.1 e0.1) :: s.drop 2
  else if tok.1 = 8 then (.zero, true, spec.fLt a e1.1 e0.1) :: s.drop 2
  else if tok.1 = 9 then (.zero, true, spec.fLe a e1.1 e0.1) :: s.drop 2
  else if tok.1 = 10 then (.zero, true, spec.fNot a e0.2.2) :: s.drop 1
  else if tok.1 = 11 then (.zero, true, spec.fAnd a e1.2.2 e0.2.2) :: s.drop 2
  else if tok.1 = 12 then (.zero, true, spec.fOr a e1.2.2 e0.2.2) :: s.drop 2
  else if tok.1 = 13 then (.zero, true, spec.fAll a e0.2.2) :: s.drop 1
  else if tok.1 = 14 then (.zero, true, spec.fEx a e0.2.2) :: s.drop 1
  else s

def runFormulaRec {A F : Type*} (spec : FormulaRecSpec A F) (a : A)
    (c : Code) (s : List (RecStackItem F)) : List (RecStackItem F) :=
  c.foldl (stepFormulaRec spec a) s

theorem runFormulaRec_append {A F : Type*} (spec : FormulaRecSpec A F) (a : A)
    (c1 c2 : Code) (s : List (RecStackItem F)) :
    runFormulaRec spec a (c1 ++ c2) s = runFormulaRec spec a c2 (runFormulaRec spec a c1 s) :=
  List.foldl_append

theorem runFormulaRec_term_code {A F : Type*} (spec : FormulaRecSpec A F) (a : A)
    (t : Term) (s : List (RecStackItem F)) :
    runFormulaRec spec a t.code s = (t, false, spec.defaultF) :: s := by
  induction t generalizing s with
  | var n => rfl
  | zero => rfl
  | one => rfl
  | add t1 t2 ih1 ih2 =>
    simp only [Term.code, runFormulaRec_append, ih1, ih2]
    rfl
  | mul t1 t2 ih1 ih2 =>
    simp only [Term.code, runFormulaRec_append, ih1, ih2]
    rfl
  | neg t1 ih1 =>
    simp only [Term.code, runFormulaRec_append, ih1]
    rfl

theorem runFormulaRec_formula_code {A F : Type*} (spec : FormulaRecSpec A F) (a : A)
    (p : Formula) (s : List (RecStackItem F)) :
    runFormulaRec spec a p.code s = (.zero, true, evalFormulaRec spec a p) :: s := by
  induction p generalizing s with
  | truth b =>
    cases b <;> rfl
  | eq t1 t2 =>
    simp only [Formula.code, runFormulaRec_append, runFormulaRec_term_code]
    rfl
  | lt t1 t2 =>
    simp only [Formula.code, runFormulaRec_append, runFormulaRec_term_code]
    rfl
  | le t1 t2 =>
    simp only [Formula.code, runFormulaRec_append, runFormulaRec_term_code]
    rfl
  | not p1 ih1 =>
    simp only [Formula.code, runFormulaRec_append, ih1]
    rfl
  | and p1 p2 ih1 ih2 =>
    simp only [Formula.code, runFormulaRec_append, ih1, ih2]
    rfl
  | or p1 p2 ih1 ih2 =>
    simp only [Formula.code, runFormulaRec_append, ih1, ih2]
    rfl
  | all p1 ih1 =>
    simp only [Formula.code, runFormulaRec_append, ih1]
    rfl
  | ex p1 ih1 =>
    simp only [Formula.code, runFormulaRec_append, ih1]
    rfl

theorem evalFormulaRec_eq_run {A F : Type*} (spec : FormulaRecSpec A F) (a : A) (p : Formula) :
    evalFormulaRec spec a p = ((runFormulaRec spec a p.code []).getD 0 (defaultRecItem spec)).2.2 := by
  rw [runFormulaRec_formula_code]
  rfl

theorem primrec_stepFormulaRec {A F : Type*} [Primcodable A] [Primcodable F]
    (spec : FormulaRecSpec A F)
    (hTruth : Primrec (fun z : A × Bool => spec.fTruth z.1 z.2))
    (hEq : Primrec (fun z : A × Term × Term => spec.fEq z.1 z.2.1 z.2.2))
    (hLt : Primrec (fun z : A × Term × Term => spec.fLt z.1 z.2.1 z.2.2))
    (hLe : Primrec (fun z : A × Term × Term => spec.fLe z.1 z.2.1 z.2.2))
    (hNot : Primrec (fun z : A × F => spec.fNot z.1 z.2))
    (hAnd : Primrec (fun z : A × F × F => spec.fAnd z.1 z.2.1 z.2.2))
    (hOr : Primrec (fun z : A × F × F => spec.fOr z.1 z.2.1 z.2.2))
    (hAll : Primrec (fun z : A × F => spec.fAll z.1 z.2))
    (hEx : Primrec (fun z : A × F => spec.fEx z.1 z.2)) :
    Primrec (fun z : A × List (RecStackItem F) × Token => stepFormulaRec spec z.1 z.2.1 z.2.2) := by
  let Z := A × List (RecStackItem F) × Token
  have ha : Primrec (fun z : Z => z.1) := Primrec.fst
  have hs : Primrec (fun z : Z => z.2.1) := Primrec.fst.comp Primrec.snd
  have htok : Primrec (fun z : Z => z.2.2) := Primrec.snd.comp Primrec.snd
  have htag : Primrec (fun z : Z => z.2.2.1) := Primrec.fst.comp htok
  have hval : Primrec (fun z : Z => z.2.2.2) := Primrec.snd.comp htok
  have he0 : Primrec (fun z : Z => z.2.1.getD 0 (defaultRecItem spec)) :=
    (Primrec.list_getD (defaultRecItem spec)).comp hs (Primrec.const 0)
  have he1 : Primrec (fun z : Z => z.2.1.getD 1 (defaultRecItem spec)) :=
    (Primrec.list_getD (defaultRecItem spec)).comp hs (Primrec.const 1)
  have ht0 : Primrec (fun z : Z => (z.2.1.getD 0 (defaultRecItem spec)).1) := Primrec.fst.comp he0
  have ht1 : Primrec (fun z : Z => (z.2.1.getD 1 (defaultRecItem spec)).1) := Primrec.fst.comp he1
  have hf0 : Primrec (fun z : Z => (z.2.1.getD 0 (defaultRecItem spec)).2.2) :=
    Primrec.snd.comp (Primrec.snd.comp he0)
  have hf1 : Primrec (fun z : Z => (z.2.1.getD 1 (defaultRecItem spec)).2.2) :=
    Primrec.snd.comp (Primrec.snd.comp he1)
  have hdrop1 : Primrec (fun z : Z => z.2.1.drop 1) :=
    Primrec.list_drop.comp (Primrec.const 1) hs
  have hdrop2 : Primrec (fun z : Z => z.2.1.drop 2) :=
    Primrec.list_drop.comp (Primrec.const 2) hs
  have mkT : ∀ {g : Z → Term} {tl : Z → List (RecStackItem F)},
      Primrec g → Primrec tl →
      Primrec (fun z : Z => (g z, false, spec.defaultF) :: tl z) :=
    fun hg htl => Primrec.list_cons.comp (hg.pair (Primrec.const (false, spec.defaultF))) htl
  have mkF : ∀ {g : Z → F} {tl : Z → List (RecStackItem F)},
      Primrec g → Primrec tl →
      Primrec (fun z : Z => (Term.zero, true, g z) :: tl z) :=
    fun hg htl => Primrec.list_cons.comp ((Primrec.const Term.zero).pair ((Primrec.const true).pair hg)) htl
  have hb0 := mkT (primrec_term_var.comp hval) hs
  have hb1 := mkT (Primrec.const Term.zero) hs
  have hb2 := mkT (Primrec.const Term.one) hs
  have hb3 := mkT (primrec_term_add.comp ht1 ht0) hdrop2
  have hb4 := mkT (primrec_term_mul.comp ht1 ht0) hdrop2
  have hb5 := mkT (primrec_term_neg.comp ht0) hdrop1
  have hb6 : Primrec (fun z : Z => (Term.zero, true, spec.fTruth z.1 (z.2.2.2 == 1)) :: z.2.1) := by
    have hbool : Primrec (fun z : Z => z.2.2.2 == 1) :=
      ((Primrec.eq.comp hval (Primrec.const 1)).decide).of_eq (fun _ => rfl)
    exact mkF (hTruth.comp (ha.pair hbool)) hs
  have hb7 := mkF (hEq.comp (ha.pair (ht1.pair ht0))) hdrop2
  have hb8 := mkF (hLt.comp (ha.pair (ht1.pair ht0))) hdrop2
  have hb9 := mkF (hLe.comp (ha.pair (ht1.pair ht0))) hdrop2
  have hb10 := mkF (hNot.comp (ha.pair hf0)) hdrop1
  have hb11 := mkF (hAnd.comp (ha.pair (hf1.pair hf0))) hdrop2
  have hb12 := mkF (hOr.comp (ha.pair (hf1.pair hf0))) hdrop2
  have hb13 := mkF (hAll.comp (ha.pair hf0)) hdrop1
  have hb14 := mkF (hEx.comp (ha.pair hf0)) hdrop1
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hb0
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hb1
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hb2
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) hb3
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) hb4
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) hb5
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) hb6
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 7)) hb7
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 8)) hb8
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 9)) hb9
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 10)) hb10
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 11)) hb11
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 12)) hb12
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 13)) hb13
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 14)) hb14 hs))))))))))))))

theorem primrec_evalFormulaRec {X A F : Type*} [Primcodable X] [Primcodable A] [Primcodable F]
    (spec : FormulaRecSpec A F) {a : X → A} {p : X → Formula}
    (ha : Primrec a) (hp : Primrec p)
    (hTruth : Primrec (fun z : A × Bool => spec.fTruth z.1 z.2))
    (hEq : Primrec (fun z : A × Term × Term => spec.fEq z.1 z.2.1 z.2.2))
    (hLt : Primrec (fun z : A × Term × Term => spec.fLt z.1 z.2.1 z.2.2))
    (hLe : Primrec (fun z : A × Term × Term => spec.fLe z.1 z.2.1 z.2.2))
    (hNot : Primrec (fun z : A × F => spec.fNot z.1 z.2))
    (hAnd : Primrec (fun z : A × F × F => spec.fAnd z.1 z.2.1 z.2.2))
    (hOr : Primrec (fun z : A × F × F => spec.fOr z.1 z.2.1 z.2.2))
    (hAll : Primrec (fun z : A × F => spec.fAll z.1 z.2))
    (hEx : Primrec (fun z : A × F => spec.fEx z.1 z.2)) :
    Primrec (fun x => evalFormulaRec spec (a x) (p x)) := by
  have hstep := primrec_stepFormulaRec spec hTruth hEq hLt hLe hNot hAnd hOr hAll hEx
  have hfold : Primrec (fun x : X => runFormulaRec spec (a x) (p x).code []) :=
    Primrec.list_foldl (primrec_formula_code.comp hp) (Primrec.const ([] : List (RecStackItem F)))
      (hstep.comp ((ha.comp Primrec.fst).pair Primrec.snd)).to₂
  have hout : Primrec (fun x : X =>
      ((runFormulaRec spec (a x) (p x).code []).getD 0 (defaultRecItem spec)).2.2) :=
    Primrec.snd.comp (Primrec.snd.comp
      ((Primrec.list_getD (defaultRecItem spec)).comp hfold (Primrec.const 0)))
  exact hout.of_eq (fun x => (evalFormulaRec_eq_run spec (a x) (p x)).symm)

theorem computable_stepFormulaRec {A F : Type*} [Primcodable A] [Primcodable F]
    (spec : FormulaRecSpec A F)
    (hTruth : Computable (fun z : A × Bool => spec.fTruth z.1 z.2))
    (hEq : Computable (fun z : A × Term × Term => spec.fEq z.1 z.2.1 z.2.2))
    (hLt : Computable (fun z : A × Term × Term => spec.fLt z.1 z.2.1 z.2.2))
    (hLe : Computable (fun z : A × Term × Term => spec.fLe z.1 z.2.1 z.2.2))
    (hNot : Computable (fun z : A × F => spec.fNot z.1 z.2))
    (hAnd : Computable (fun z : A × F × F => spec.fAnd z.1 z.2.1 z.2.2))
    (hOr : Computable (fun z : A × F × F => spec.fOr z.1 z.2.1 z.2.2))
    (hAll : Computable (fun z : A × F => spec.fAll z.1 z.2))
    (hEx : Computable (fun z : A × F => spec.fEx z.1 z.2)) :
    Computable (fun z : A × List (RecStackItem F) × Token => stepFormulaRec spec z.1 z.2.1 z.2.2) := by
  let Z := A × List (RecStackItem F) × Token
  have ha : Computable (fun z : Z => z.1) := Computable.fst
  have hs : Computable (fun z : Z => z.2.1) := Computable.fst.comp Computable.snd
  have htok : Computable (fun z : Z => z.2.2) := Computable.snd.comp Computable.snd
  have htag : Primrec (fun z : Z => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hval : Primrec (fun z : Z => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have he0 : Primrec (fun z : Z => z.2.1.getD 0 (defaultRecItem spec)) :=
    (Primrec.list_getD (defaultRecItem spec)).comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  have he1 : Primrec (fun z : Z => z.2.1.getD 1 (defaultRecItem spec)) :=
    (Primrec.list_getD (defaultRecItem spec)).comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have ht0 : Computable (fun z : Z => (z.2.1.getD 0 (defaultRecItem spec)).1) :=
    (Primrec.fst.comp he0).to_comp
  have ht1 : Computable (fun z : Z => (z.2.1.getD 1 (defaultRecItem spec)).1) :=
    (Primrec.fst.comp he1).to_comp
  have hf0 : Computable (fun z : Z => (z.2.1.getD 0 (defaultRecItem spec)).2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp he0)).to_comp
  have hf1 : Computable (fun z : Z => (z.2.1.getD 1 (defaultRecItem spec)).2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp he1)).to_comp
  have hdrop1 : Computable (fun z : Z => z.2.1.drop 1) :=
    (Primrec.list_drop.comp (Primrec.const 1) (Primrec.fst.comp Primrec.snd)).to_comp
  have hdrop2 : Computable (fun z : Z => z.2.1.drop 2) :=
    (Primrec.list_drop.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd)).to_comp
  have mkT : ∀ {g : Z → Term} {tl : Z → List (RecStackItem F)},
      Computable g → Computable tl →
      Computable (fun z : Z => (g z, false, spec.defaultF) :: tl z) :=
    fun hg htl => Computable.list_cons.comp (hg.pair (Computable.const (false, spec.defaultF))) htl
  have mkF : ∀ {g : Z → F} {tl : Z → List (RecStackItem F)},
      Computable g → Computable tl →
      Computable (fun z : Z => (Term.zero, true, g z) :: tl z) :=
    fun hg htl => Computable.list_cons.comp ((Computable.const Term.zero).pair ((Computable.const true).pair hg)) htl
  have eqTag (n : ℕ) : Computable (fun z : Z => decide (z.2.2.1 = n)) :=
    ((Primrec.eq.comp htag (Primrec.const n)).decide).to_comp
  have iteTag (n : ℕ) {th el : Z → List (RecStackItem F)}
      (hth : Computable th) (hel : Computable el) :
      Computable (fun z : Z => if z.2.2.1 = n then th z else el z) :=
    (Computable.cond (eqTag n) hth hel).of_eq (fun z => by by_cases h : z.2.2.1 = n <;> simp [h])
  have hb0 := mkT (primrec_term_var.to_comp.comp hval.to_comp) hs
  have hb1 := mkT (Computable.const Term.zero) hs
  have hb2 := mkT (Computable.const Term.one) hs
  have hb3 := mkT (primrec_term_add.to_comp.comp ht1 ht0) hdrop2
  have hb4 := mkT (primrec_term_mul.to_comp.comp ht1 ht0) hdrop2
  have hb5 := mkT (primrec_term_neg.to_comp.comp ht0) hdrop1
  have hb6 : Computable (fun z : Z => (Term.zero, true, spec.fTruth z.1 (z.2.2.2 == 1)) :: z.2.1) := by
    have hbool : Computable (fun z : Z => z.2.2.2 == 1) :=
      (((Primrec.eq.comp hval (Primrec.const 1)).decide).of_eq (fun _ => rfl)).to_comp
    exact mkF (hTruth.comp (ha.pair hbool)) hs
  have hb7 := mkF (hEq.comp (ha.pair (ht1.pair ht0))) hdrop2
  have hb8 := mkF (hLt.comp (ha.pair (ht1.pair ht0))) hdrop2
  have hb9 := mkF (hLe.comp (ha.pair (ht1.pair ht0))) hdrop2
  have hb10 := mkF (hNot.comp (ha.pair hf0)) hdrop1
  have hb11 := mkF (hAnd.comp (ha.pair (hf1.pair hf0))) hdrop2
  have hb12 := mkF (hOr.comp (ha.pair (hf1.pair hf0))) hdrop2
  have hb13 := mkF (hAll.comp (ha.pair hf0)) hdrop1
  have hb14 := mkF (hEx.comp (ha.pair hf0)) hdrop1
  exact iteTag 0 hb0 (iteTag 1 hb1 (iteTag 2 hb2 (iteTag 3 hb3 (iteTag 4 hb4
    (iteTag 5 hb5 (iteTag 6 hb6 (iteTag 7 hb7 (iteTag 8 hb8 (iteTag 9 hb9
    (iteTag 10 hb10 (iteTag 11 hb11 (iteTag 12 hb12 (iteTag 13 hb13 (iteTag 14 hb14 hs))))))))))))))

theorem computable_evalFormulaRec {A F : Type*} [Primcodable A] [Primcodable F]
    (spec : FormulaRecSpec A F) {p : A → Formula}
    (hp : Computable p)
    (hTruth : Computable (fun z : A × Bool => spec.fTruth z.1 z.2))
    (hEq : Computable (fun z : A × Term × Term => spec.fEq z.1 z.2.1 z.2.2))
    (hLt : Computable (fun z : A × Term × Term => spec.fLt z.1 z.2.1 z.2.2))
    (hLe : Computable (fun z : A × Term × Term => spec.fLe z.1 z.2.1 z.2.2))
    (hNot : Computable (fun z : A × F => spec.fNot z.1 z.2))
    (hAnd : Computable (fun z : A × F × F => spec.fAnd z.1 z.2.1 z.2.2))
    (hOr : Computable (fun z : A × F × F => spec.fOr z.1 z.2.1 z.2.2))
    (hAll : Computable (fun z : A × F => spec.fAll z.1 z.2))
    (hEx : Computable (fun z : A × F => spec.fEx z.1 z.2)) :
    Computable (fun a => evalFormulaRec spec a (p a)) := by
  have hstep := computable_stepFormulaRec spec hTruth hEq hLt hLe hNot hAnd hOr hAll hEx
  have hfold : Computable (fun a : A => runFormulaRec spec a (p a).code []) :=
    computable_list_foldl (primrec_formula_code.to_comp.comp hp) (Computable.const []) hstep
  have hout : Computable (fun a : A =>
      ((runFormulaRec spec a (p a).code []).getD 0 (defaultRecItem spec)).2.2) :=
    (Primrec.snd.comp (Primrec.snd.comp
      ((Primrec.list_getD (defaultRecItem spec)).comp Primrec.id (Primrec.const 0)))).to_comp.comp hfold
  exact hout.of_eq (fun a => (evalFormulaRec_eq_run spec a (p a)).symm)

def leafMarker (n : ℕ) : Formula := .le (.var n) .zero

theorem primrec_leafMarker : Primrec leafMarker :=
  primrec_formula_le.comp primrec_term_var (Primrec.const Term.zero)

def isLeafMarkerTerms (t1 t2 : Term) : Option ℕ :=
  match t1, t2 with
  | .var n, .zero => some n
  | _, _ => none

theorem term_code_inj {t1 t2 : Term} : t1.code = t2.code ↔ t1 = t2 :=
  ⟨fun h => Option.some.inj (by rw [← decodeTerm_code t1, ← decodeTerm_code t2, h]),
   congrArg Term.code⟩

theorem isLeafMarkerTerms_eq (t1 t2 : Term) :
    isLeafMarkerTerms t1 t2 =
      if t2.code = [(1, 0)] ∧ t1.code = [(0, (t1.code.getD 0 (0, 0)).2)] then
        some (t1.code.getD 0 (0, 0)).2
      else none := by
  have hz : t2.code = [(1, 0)] ↔ t2 = Term.zero := term_code_inj (t2 := Term.zero)
  have hv : ∀ m : ℕ, t1.code = [(0, m)] ↔ t1 = Term.var m :=
    fun m => term_code_inj (t2 := Term.var m)
  simp only [hz, hv]
  cases t1 <;> cases t2 <;> simp [isLeafMarkerTerms, Term.code]

theorem primrec_isLeafMarkerTerms : Primrec₂ isLeafMarkerTerms := by
  have hc1 : Primrec (fun z : Term × Term => z.1.code) := primrec_term_code.comp Primrec.fst
  have hc2 : Primrec (fun z : Term × Term => z.2.code) := primrec_term_code.comp Primrec.snd
  have he0 : Primrec (fun z : Term × Term => z.1.code.getD 0 (0, 0)) :=
    (Primrec.list_getD (0, 0)).comp hc1 (Primrec.const 0)
  have hvarCode : Primrec (fun z : Term × Term => ([(0, (z.1.code.getD 0 (0, 0)).2)] : Code)) :=
    Primrec.list_cons.comp ((Primrec.const 0).pair (Primrec.snd.comp he0)) (Primrec.const [])
  have hcond : PrimrecPred (fun z : Term × Term =>
      z.2.code = [(1, 0)] ∧ z.1.code = [(0, (z.1.code.getD 0 (0, 0)).2)]) :=
    PrimrecPred.and (Primrec.eq.comp hc2 (Primrec.const [(1, 0)]))
      (Primrec.eq.comp hc1 hvarCode)
  exact (Primrec.ite hcond (Primrec.option_some.comp (Primrec.snd.comp he0))
    (Primrec.const none)).of_eq (fun z => (isLeafMarkerTerms_eq z.1 z.2).symm)

def substEx (f : ℕ → Formula) : Formula → Formula
  | .truth b => .truth b
  | .eq t1 t2 => .eq t1 t2
  | .lt t1 t2 => .lt t1 t2
  | .le t1 t2 =>
      match isLeafMarkerTerms t1 t2 with
      | some n => f n
      | none => .le t1 t2
  | .not p => .not (substEx f p)
  | .and p q => .and (substEx f p) (substEx f q)
  | .or p q => .or (substEx f p) (substEx f q)
  | .all p => .all (substEx f p)
  | .ex p => .ex (substEx f p)

@[simp] theorem substEx_leafMarker (f : ℕ → Formula) (n : ℕ) :
    substEx f (leafMarker n) = f n := rfl

@[simp] theorem substEx_branch (f : ℕ → Formula) (test yes no : Formula) :
    substEx f (branch test yes no) = branch (substEx f test) (substEx f yes) (substEx f no) := rfl

theorem substEx_sizeCases (f : ℕ → Formula) (p : TermPoly) (k : ℕ → Formula) :
    substEx f (sizeCases p k) = sizeCases p (fun n => substEx f (k n)) := by
  induction p generalizing k with
  | nil => rfl
  | cons a p ih =>
    simp only [sizeCases, ih]
    congr 1
    funext n
    by_cases hn : n = 0
    · simp [hn, substEx_branch, substEx]
    · simp [hn]

theorem substEx_leadingCases (f : ℕ → Formula) (p : TermPoly) (k : Term → Formula) :
    substEx f (leadingCases p k) = leadingCases p (fun t => substEx f (k t)) := by
  unfold leadingCases
  rw [substEx_sizeCases]

theorem substEx_pseudoDivLoopCases (f : ℕ → Formula) (q : TermPoly) (sq : ℕ) (cq : Term)
    (fuel c : ℕ) (a r : TermPoly) (k : ℕ → TermPoly → TermPoly → Formula) :
    substEx f (pseudoDivLoopCases q sq cq fuel c a r k) =
      pseudoDivLoopCases q sq cq fuel c a r (fun c' a' r' => substEx f (k c' a' r')) := by
  induction fuel generalizing c a r with
  | zero => rfl
  | succ n ih =>
    unfold pseudoDivLoopCases
    rw [substEx_sizeCases]
    congr 1
    funext sr
    by_cases h : sr < sq
    · simp [h]
    · simp only [if_neg h, substEx_leadingCases]
      congr 1
      funext cr
      exact ih (c + 1) _ _

theorem substEx_pseudoDivCases (f : ℕ → Formula) (p q : TermPoly)
    (k : ℕ → TermPoly → TermPoly → Formula) :
    substEx f (pseudoDivCases p q k) =
      pseudoDivCases p q (fun c a r => substEx f (k c a r)) := by
  unfold pseudoDivCases
  rw [substEx_sizeCases]
  congr 1
  funext sq
  by_cases h : sq = 0
  · simp [h]
  · simp only [if_neg h, substEx_leadingCases]
    congr 1
    funext cq
    exact substEx_pseudoDivLoopCases f q sq cq p.length 0 [] p k

def leavesOfFormula : Formula → List ℕ
  | .truth _ => []
  | .eq _ _ => []
  | .lt _ _ => []
  | .le t1 t2 =>
      match isLeafMarkerTerms t1 t2 with
      | some n => [n]
      | none => []
  | .not p => leavesOfFormula p
  | .and p q => leavesOfFormula p ++ leavesOfFormula q
  | .or p q => leavesOfFormula p ++ leavesOfFormula q
  | .all p => leavesOfFormula p
  | .ex p => leavesOfFormula p

def leavesRecSpec : FormulaRecSpec Unit (List ℕ) where
  defaultF := []
  fTruth := fun _ _ => []
  fEq := fun _ _ _ => []
  fLt := fun _ _ _ => []
  fLe := fun _ t1 t2 => ((isLeafMarkerTerms t1 t2).map (fun n => [n])).getD []
  fNot := fun _ l => l
  fAnd := fun _ l1 l2 => l1 ++ l2
  fOr := fun _ l1 l2 => l1 ++ l2
  fAll := fun _ l => l
  fEx := fun _ l => l

theorem leavesOfFormula_eq_rec (p : Formula) :
    leavesOfFormula p = evalFormulaRec leavesRecSpec () p := by
  induction p <;> simp_all [leavesOfFormula, evalFormulaRec, leavesRecSpec]
  case le t1 t2 => cases isLeafMarkerTerms t1 t2 <;> rfl

theorem primrec_leavesOfFormula : Primrec leavesOfFormula := by
  have hLe : Primrec (fun z : Unit × Term × Term =>
      ((isLeafMarkerTerms z.2.1 z.2.2).map (fun n => [n])).getD ([] : List ℕ)) := by
    have his : Primrec (fun z : Unit × Term × Term => isLeafMarkerTerms z.2.1 z.2.2) :=
      primrec_isLeafMarkerTerms.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    have hmap : Primrec (fun z : Unit × Term × Term =>
        (isLeafMarkerTerms z.2.1 z.2.2).map (fun n => [n])) :=
      Primrec.option_map his (Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : List ℕ))).to₂
    exact Primrec.option_getD.comp hmap (Primrec.const ([] : List ℕ))
  have hrec : Primrec (fun p : Formula => evalFormulaRec leavesRecSpec () p) :=
    primrec_evalFormulaRec leavesRecSpec (Primrec.const ()) Primrec.id
      (Primrec.const ([] : List ℕ))
      (Primrec.const ([] : List ℕ))
      (Primrec.const ([] : List ℕ))
      hLe
      Primrec.snd
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      Primrec.snd
      Primrec.snd
  exact hrec.of_eq (fun p => (leavesOfFormula_eq_rec p).symm)

def lookupFormula (table : List (ℕ × Formula)) (n : ℕ) : Formula :=
  table.foldl (fun acc p => if p.1 = n then p.2 else acc) (Formula.truth false)

theorem primrec_lookupFormula : Primrec₂ lookupFormula := by
  let Z := List (ℕ × Formula) × ℕ
  have hf : Primrec (fun z : Z => z.1) := Primrec.fst
  have hg : Primrec (fun _ : Z => Formula.truth false) := Primrec.const (Formula.truth false)
  have hn : Primrec (fun w : Z × Formula × (ℕ × Formula) => w.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hp1 : Primrec (fun w : Z × Formula × (ℕ × Formula) => w.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hp2 : Primrec (fun w : Z × Formula × (ℕ × Formula) => w.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hacc : Primrec (fun w : Z × Formula × (ℕ × Formula) => w.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hstep : Primrec₂ (fun (z : Z) (sp : Formula × (ℕ × Formula)) =>
      if sp.2.1 = z.2 then sp.2.2 else sp.1) :=
    (Primrec.ite (Primrec.eq.comp hp1 hn) hp2 hacc).to₂
  exact (Primrec.list_foldl hf hg hstep).to₂

private theorem foldl_lookupFormula_map (f : ℕ → Formula) (ns : List ℕ) (n : ℕ) (init : Formula) :
    (ns.map (fun m => (m, f m))).foldl (fun acc p => if p.1 = n then p.2 else acc) init =
      if n ∈ ns then f n else init := by
  induction ns generalizing init with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.foldl_cons, ih, List.mem_cons]
    by_cases hmn : m = n
    · subst hmn
      by_cases hmem : m ∈ ms <;> simp [hmem]
    · have hne : n ≠ m := fun h => hmn h.symm
      by_cases hmem : n ∈ ms <;> simp [hmn, hne, hmem]

theorem lookupFormula_map (f : ℕ → Formula) (ns : List ℕ) (n : ℕ) (hn : n ∈ ns) :
    lookupFormula (ns.map (fun m => (m, f m))) n = f n := by
  unfold lookupFormula
  rw [foldl_lookupFormula_map, if_pos hn]

def fillLeaves (tpl : Formula) (table : List (ℕ × Formula)) : Formula :=
  substEx (lookupFormula table) tpl

def fillLeavesRecSpec : FormulaRecSpec (List (ℕ × Formula)) Formula where
  defaultF := .truth false
  fTruth := fun _ b => .truth b
  fEq := fun _ t1 t2 => .eq t1 t2
  fLt := fun _ t1 t2 => .lt t1 t2
  fLe := fun table t1 t2 =>
    ((isLeafMarkerTerms t1 t2).map (lookupFormula table)).getD (.le t1 t2)
  fNot := fun _ p => .not p
  fAnd := fun _ p q => .and p q
  fOr := fun _ p q => .or p q
  fAll := fun _ p => .all p
  fEx := fun _ p => .ex p

theorem substEx_eq_rec (f : ℕ → Formula) (tpl : Formula) :
    substEx f tpl = evalFormulaRec
      { fillLeavesRecSpec with
        fLe := fun _ t1 t2 => ((isLeafMarkerTerms t1 t2).map f).getD (.le t1 t2) } [] tpl := by
  induction tpl <;> simp_all [substEx, evalFormulaRec, fillLeavesRecSpec]
  case le t1 t2 => cases isLeafMarkerTerms t1 t2 <;> rfl

theorem fillLeaves_eq_rec (tpl : Formula) (table : List (ℕ × Formula)) :
    fillLeaves tpl table = evalFormulaRec fillLeavesRecSpec table tpl := by
  unfold fillLeaves
  induction tpl <;> simp_all [substEx, evalFormulaRec, fillLeavesRecSpec]
  case le t1 t2 => cases isLeafMarkerTerms t1 t2 <;> rfl

theorem primrec_fillLeaves : Primrec₂ fillLeaves := by
  let A := List (ℕ × Formula)
  have hLe : Primrec (fun z : A × Term × Term =>
      ((isLeafMarkerTerms z.2.1 z.2.2).map (lookupFormula z.1)).getD (Formula.le z.2.1 z.2.2)) := by
    have his : Primrec (fun z : A × Term × Term => isLeafMarkerTerms z.2.1 z.2.2) :=
      primrec_isLeafMarkerTerms.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    have hnone : Primrec (fun z : A × Term × Term => Formula.le z.2.1 z.2.2) :=
      primrec_formula_le.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    have hsome : Primrec (fun w : (A × Term × Term) × ℕ => lookupFormula w.1.1 w.2) :=
      primrec_lookupFormula.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
    exact Primrec.option_getD.comp (Primrec.option_map his hsome.to₂) hnone
  have hrec : Primrec (fun z : Formula × A => evalFormulaRec fillLeavesRecSpec z.2 z.1) :=
    primrec_evalFormulaRec fillLeavesRecSpec Primrec.snd Primrec.fst
      (primrec_formula_truth.comp Primrec.snd)
      (primrec_formula_eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (primrec_formula_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      hLe
      (primrec_formula_not.comp Primrec.snd)
      (primrec_formula_and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (primrec_formula_or.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (primrec_formula_all.comp Primrec.snd)
      (primrec_formula_ex.comp Primrec.snd)
  exact hrec.of_eq (fun z => (fillLeaves_eq_rec z.1 z.2).symm)

theorem substEx_congr_on_leaves {f g : ℕ → Formula} (tpl : Formula)
    (hfg : ∀ n ∈ leavesOfFormula tpl, f n = g n) :
    substEx f tpl = substEx g tpl := by
  induction tpl with
  | truth _ => rfl
  | eq _ _ => rfl
  | lt _ _ => rfl
  | le t1 t2 =>
    simp only [substEx, leavesOfFormula] at hfg ⊢
    cases h : isLeafMarkerTerms t1 t2 with
    | none => rfl
    | some n =>
      rw [h] at hfg
      exact hfg n (List.mem_singleton_self n)
  | not p ih =>
    simp only [substEx, leavesOfFormula] at hfg ⊢
    exact congrArg Formula.not (ih hfg)
  | and p q ihp ihq =>
    simp only [substEx, leavesOfFormula, List.mem_append] at hfg ⊢
    exact congrArg₂ Formula.and (ihp (fun n hn => hfg n (Or.inl hn)))
      (ihq (fun n hn => hfg n (Or.inr hn)))
  | or p q ihp ihq =>
    simp only [substEx, leavesOfFormula, List.mem_append] at hfg ⊢
    exact congrArg₂ Formula.or (ihp (fun n hn => hfg n (Or.inl hn)))
      (ihq (fun n hn => hfg n (Or.inr hn)))
  | all p ih =>
    simp only [substEx, leavesOfFormula] at hfg ⊢
    exact congrArg Formula.all (ih hfg)
  | ex p ih =>
    simp only [substEx, leavesOfFormula] at hfg ⊢
    exact congrArg Formula.ex (ih hfg)

theorem fillLeaves_map_eq_substEx (f : ℕ → Formula) (tpl : Formula) :
    fillLeaves tpl ((leavesOfFormula tpl).map (fun n => (n, f n))) = substEx f tpl :=
  substEx_congr_on_leaves tpl (fun n hn => lookupFormula_map f (leavesOfFormula tpl) n hn)

def bindLeaves (tpl : Formula) (recCall : ℕ → Part Formula) : Part Formula :=
  (traversePart (fun n => (recCall n).map (fun res => (n, res)))
    (leavesOfFormula tpl)).map (fillLeaves tpl)

theorem bindLeaves_eq_some (tpl : Formula) (recCall : ℕ → Part Formula) (f : ℕ → Formula)
    (h : ∀ n ∈ leavesOfFormula tpl, recCall n = Part.some (f n)) :
    bindLeaves tpl recCall = Part.some (substEx f tpl) := by
  unfold bindLeaves
  have htrav : traversePart (fun n => (recCall n).map (fun res => (n, res)))
      (leavesOfFormula tpl) =
      Part.some ((leavesOfFormula tpl).map (fun n => (n, f n))) := by
    refine traversePart_eq_some_map _ _ _ (fun n hn => ?_)
    rw [h n hn, Part.map_some]
  rw [htrav, Part.map_some, fillLeaves_map_eq_substEx]

theorem partrec_bindLeaves {A : Type*} [Primcodable A]
    {tpl : A → Formula} {recCall : A → ℕ → Part Formula}
    (htpl : Computable tpl) (hrec : Partrec₂ recCall) :
    Partrec (fun a => bindLeaves (tpl a) (recCall a)) := by
  have hleaves : Computable (fun a : A => leavesOfFormula (tpl a)) :=
    primrec_leavesOfFormula.to_comp.comp htpl
  have hstep : Partrec₂ (fun (a : A) (n : ℕ) => (recCall a n).map (fun res => (n, res))) :=
    (Partrec.map hrec (((Computable.snd.comp Computable.fst).pair Computable.snd).to₂)).to₂
  have htrav : Partrec (fun a : A =>
      traversePart (fun n => (recCall a n).map (fun res => (n, res))) (leavesOfFormula (tpl a))) :=
    (partrec_traversePart hstep).comp Computable.id hleaves
  have hfill : Computable₂ (fun (a : A) (table : List (ℕ × Formula)) => fillLeaves (tpl a) table) :=
    (primrec_fillLeaves.to_comp.comp (htpl.comp Computable.fst) Computable.snd).to₂
  exact Partrec.map htrav hfill

theorem computable_substEx {A : Type*} [Primcodable A]
    {tpl : A → Formula} {f : A → ℕ → Formula}
    (htpl : Computable tpl) (hf : Computable₂ f) :
    Computable (fun a => substEx (f a) (tpl a)) :=
  (partrec_bindLeaves htpl hf.partrec₂).of_eq
    (fun a => bindLeaves_eq_some (tpl a) (fun n => Part.some (f a n)) (f a) (fun _ _ => rfl))

def stepLeafTemplate {S : Type*} [Primcodable S]
    (tpl : S → Formula) (recCall : S → Part Formula) (s : S) : Part Formula :=
  bindLeaves (tpl s) (fun n =>
    (Encodable.decode (α := S) n).casesOn (Part.some (Formula.truth false)) recCall)

theorem computable_of_leaf_template {S : Type*} [Primcodable S]
    (F : S → Formula) (fuel : S → ℕ) (tpl : S → Formula)
    (htpl : Computable tpl)
    (hleaves : ∀ s : S, ∀ n ∈ leavesOfFormula (tpl s),
      ∃ s' : S, Encodable.decode (α := S) n = some s' ∧ fuel s' < fuel s)
    (heq : ∀ s : S,
      substEx (fun n => (Encodable.decode (α := S) n).casesOn (Formula.truth false) F) (tpl s) = F s) :
    Computable F := by
  have hbody : Partrec₂ (fun c (s : S) => stepLeafTemplate tpl (evalFormulaAt c) s) := by
    change Partrec (fun p : Nat.Partrec.Code × S => stepLeafTemplate tpl (evalFormulaAt p.1) p.2)
    refine partrec_bindLeaves (htpl.comp Computable.snd) ?_
    have hdec : Computable (fun q : (Nat.Partrec.Code × S) × ℕ => Encodable.decode (α := S) q.2) :=
      (Computable.decode (α := S)).comp Computable.snd
    have hcall : Partrec (fun w : ((Nat.Partrec.Code × S) × ℕ) × S =>
        evalFormulaAt w.1.1.1 w.2) :=
      partrec_evalFormulaAt.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd
    exact (Partrec.optionCasesOn_right hdec (Computable.const (Formula.truth false)) hcall.to₂).to₂
  refine computable_of_decreasing_step_formula F fuel (stepLeafTemplate tpl) hbody ?_
  intro recCall s ih
  unfold stepLeafTemplate
  rw [bindLeaves_eq_some (tpl s) _
    (fun n => (Encodable.decode (α := S) n).casesOn (Formula.truth false) F)]
  · exact congrArg Part.some (heq s)
  · intro n hn
    rcases hleaves s n hn with ⟨s', hdec, hlt⟩
    rw [hdec]
    exact ih s' hlt

end Grunbaum2003.FormulaCompiler.Parametric

open scoped BigOperators

namespace Grunbaum2003.FormulaCompiler.Parametric

def termPow (t : Term) (n : ℕ) : Term :=
  (List.range n).foldl (fun acc _ => Term.mul acc t) Term.one

theorem primrec_termPow : Primrec₂ termPow := by
  let Z := Term × ℕ
  have hrng : Primrec (fun z : Z => List.range z.2) :=
    Primrec.list_range.comp Primrec.snd
  have hinit : Primrec (fun _ : Z => Term.one) := Primrec.const Term.one
  have hstep : Primrec₂ (fun (z : Z) (p : Term × ℕ) => Term.mul p.1 z.1) :=
    (primrec_term_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)).to₂
  exact (Primrec.list_foldl hrng hinit hstep).to₂

private theorem eval_foldl_mul_range (t : Term) (n : ℕ) (acc : Term) (ρ : ℕ → ℝ) :
    ((List.range n).foldl (fun acc _ => Term.mul acc t) acc).eval ρ =
      acc.eval ρ * (t.eval ρ) ^ n := by
  induction n generalizing acc with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Term.eval, ih, pow_succ]
    ring

@[simp] theorem eval_termPow (t : Term) (n : ℕ) (ρ : ℕ → ℝ) :
    (termPow t n).eval ρ = (t.eval ρ) ^ n := by
  simp [termPow, eval_foldl_mul_range, Term.eval]

def deriv : TermPoly → TermPoly
  | [] => []
  | _ :: p => add p (.zero :: deriv p)

private def derivStep (a : Term) (acc : TermPoly × TermPoly) : TermPoly × TermPoly :=
  (a :: acc.1, add acc.1 (.zero :: acc.2))

private theorem deriv_eq_foldr_snd (p : TermPoly) :
    p.foldr derivStep ([], []) = (p, deriv p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.foldr_cons, ih, derivStep, deriv]

theorem primrec_deriv : Primrec deriv := by
  have hstep : Primrec₂ (fun (_ : TermPoly) (p : Term × (TermPoly × TermPoly)) =>
      derivStep p.1 p.2) := by
    have ha : Primrec (fun w : TermPoly × Term × (TermPoly × TermPoly) => w.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hacc1 : Primrec (fun w : TermPoly × Term × (TermPoly × TermPoly) => w.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hacc2 : Primrec (fun w : TermPoly × Term × (TermPoly × TermPoly) => w.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    exact ((Primrec.list_cons.comp ha hacc1).pair
      (primrec_poly_add.comp hacc1
        (Primrec.list_cons.comp (Primrec.const Term.zero) hacc2))).to₂
  have hfold : Primrec (fun p : TermPoly => (p.foldr derivStep ([], [])).2) :=
    Primrec.snd.comp (Primrec.list_foldr Primrec.id (Primrec.const ([], [])) hstep)
  exact hfold.of_eq (fun p => by rw [deriv_eq_foldr_snd])

theorem specialize_deriv (ρ : ℕ → ℝ) (p : TermPoly) :
    specialize ρ (deriv p) = (specialize ρ p).derivative := by
  induction p with
  | nil => simp [deriv, specialize]
  | cons a p ih =>
    simp only [deriv, specialize_add, specialize, Term.eval, Polynomial.C_0, zero_add, ih,
      Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.derivative_X, mul_one]
    ring

def nextModTermPoly (cq : Term) (c : ℕ) (r : TermPoly) : TermPoly :=
  neg (scale (termPow cq c) r)

theorem primrec_nextModTermPoly :
    Primrec (fun z : Term × ℕ × TermPoly => nextModTermPoly z.1 z.2.1 z.2.2) :=
  primrec_poly_neg.comp
    (primrec_poly_scale.comp
      (primrec_termPow.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))

theorem specialize_nextModTermPoly (ρ : ℕ → ℝ) (cq : Term) (c : ℕ) (r : TermPoly) :
    specialize ρ (nextModTermPoly cq c r) =
      -(Polynomial.C ((cq.eval ρ) ^ c) * specialize ρ r) := by
  simp [nextModTermPoly, specialize_neg, specialize_scale, eval_termPow]

def minftyTerm (s : ℕ) (c : Term) : Term :=
  if (s - 1) % 2 = 0 then c else .neg c

theorem primrec_minftyTerm : Primrec₂ minftyTerm := by
  have hcond : PrimrecPred (fun z : ℕ × Term => (z.1 - 1) % 2 = 0) :=
    Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)) (Primrec.const 2))
      (Primrec.const 0)
  exact (Primrec.ite hcond Primrec.snd (primrec_term_neg.comp Primrec.snd)).to₂

theorem eval_minftyTerm (s : ℕ) (c : Term) (ρ : ℕ → ℝ) :
    (minftyTerm s c).eval ρ = minftySignFactor s * c.eval ρ := by
  unfold minftyTerm minftySignFactor
  rcases Nat.even_or_odd (s - 1) with hev | hod
  · have hmod : (s - 1) % 2 = 0 := Nat.even_iff.mp hev
    rw [if_pos hmod, Even.neg_one_pow hev, one_mul]
  · have hmod : (s - 1) % 2 ≠ 0 := by
      rw [Nat.odd_iff.mp hod]
      decide
    rw [if_neg hmod, Odd.neg_one_pow hod, Term.eval, neg_one_mul]

theorem eval_coefficient_of_specializedSize_ne_zero (p : TermPoly) (ρ : ℕ → ℝ)
    (hs : specializedSize ρ p ≠ 0) :
    (coefficient p (specializedSize ρ p - 1)).eval ρ = (specialize ρ p).leadingCoeff := by
  have h := eval_leading_selected p ρ
  rwa [if_neg hs] at h

def inftyJumpBranch (sp sq : ℕ) (cp cq : Term) (k : ℕ → ℕ → Formula) : Formula :=
  branch (.lt (.mul (minftyTerm sp cp) (minftyTerm sq cq)) .zero)
    (branch (.lt (.mul cp cq) .zero) (k 0 0) (k 1 0))
    (branch (.lt (.mul cp cq) .zero) (k 0 1) (k 0 0))

theorem holds_inftyJumpBranch (sp sq : ℕ) (cp cq : Term) (k : ℕ → ℕ → Formula)
    (ρ : ℕ → ℝ) (p q : Polynomial ℝ) (P : ℤ → Prop)
    (hsp : sp = realSize p) (hsq : sq = realSize q)
    (hcp : cp.eval ρ = p.leadingCoeff) (hcq : cq.eval ρ = q.leadingCoeff)
    (hk : ∀ dp dm : ℕ, (k dp dm).Holds ρ ↔ P ((dp : ℤ) - (dm : ℤ))) :
    (inftyJumpBranch sp sq cp cq k).Holds ρ ↔ P (inftyJump p q) := by
  classical
  subst sp sq
  unfold inftyJumpBranch inftyJump
  have hm : (minftyTerm (realSize p) cp).eval ρ * (minftyTerm (realSize q) cq).eval ρ =
      minftyCoeff p * minftyCoeff q := by
    simp [eval_minftyTerm, hcp, hcq, minftyCoeff]
  have hp : cp.eval ρ * cq.eval ρ = p.leadingCoeff * q.leadingCoeff := by
    simp [hcp, hcq]
  simp only [holds_branch, Formula.Holds, Term.eval, hm, hp, hk]
  by_cases h1 : minftyCoeff p * minftyCoeff q < 0 <;>
    by_cases h2 : p.leadingCoeff * q.leadingCoeff < 0 <;>
    simp [h1, h2]

noncomputable def realModsChangesAux : ℕ → Polynomial ℝ → Polynomial ℝ → ℤ
  | 0, _, _ => 0
  | n + 1, p, q =>
      if realSize p = 0 then 0
      else if realSize q = 0 then 0
      else inftyJump p q + realModsChangesAux n q (realNextMod p q)

theorem realMods_eq_singleton_of_right_zero {p : Polynomial ℝ} (hp : p ≠ 0) :
    realMods p 0 = [p] := by
  rw [realMods_cons p 0 hp, realMods_zero_left]

@[simp] theorem realChangesPoly_nil : realChangesPoly [] = 0 := by
  simp [realChangesPoly, realSeqMInfty, realSeqPInfty]

@[simp] theorem realChangesPoly_singleton (p : Polynomial ℝ) : realChangesPoly [p] = 0 := by
  simp [realChangesPoly, realSeqMInfty, realSeqPInfty]

theorem realModsChangesAux_eq_realChangesPoly_realMods (fuel : ℕ) (p q : Polynomial ℝ)
    (hf : realSize q ≤ fuel) :
    realModsChangesAux fuel p q = realChangesPoly (realMods p q) := by
  induction fuel using Nat.strongRecOn generalizing p q with
  | ind fuel ih =>
    cases fuel with
    | zero =>
      have hq0 : realSize q = 0 := Nat.eq_zero_of_le_zero hf
      have hq : q = 0 := (realSize_eq_zero_iff q).mp hq0
      subst hq
      by_cases hp : p = 0
      · subst hp
        simp [realModsChangesAux, realMods_zero_left]
      · simp [realModsChangesAux, realMods_eq_singleton_of_right_zero hp]
    | succ n =>
      unfold realModsChangesAux
      by_cases hp0 : realSize p = 0
      · have hp : p = 0 := (realSize_eq_zero_iff p).mp hp0
        subst hp
        simp [hp0, realMods_zero_left]
      · have hp : p ≠ 0 := (realSize_eq_zero_iff p).not.mp hp0
        rw [if_neg hp0]
        by_cases hq0 : realSize q = 0
        · have hq : q = 0 := (realSize_eq_zero_iff q).mp hq0
          subst hq
          simp [hq0, realMods_eq_singleton_of_right_zero hp]
        · have hq : q ≠ 0 := (realSize_eq_zero_iff q).not.mp hq0
          rw [if_neg hq0]
          have hlt : realSize (realNextMod p q) < realSize q :=
            realSize_realNextMod_lt p q hq
          have hle : realSize (realNextMod p q) ≤ n := by omega
          rw [ih n (Nat.lt_succ_self n) q (realNextMod p q) hle,
              realChangesPoly_realMods_step hp hq]

@[simp] theorem leavesOfFormula_leafMarker (n : ℕ) :
    leavesOfFormula (leafMarker n) = [n] := rfl

theorem mem_leavesOfFormula_branch_eq {a b : Term} {yes no : Formula} {m : ℕ}
    (hm : m ∈ leavesOfFormula (branch (.eq a b) yes no)) :
    m ∈ leavesOfFormula yes ∨ m ∈ leavesOfFormula no := by
  simpa [branch, leavesOfFormula] using hm

theorem mem_leavesOfFormula_branch_lt {a b : Term} {yes no : Formula} {m : ℕ}
    (hm : m ∈ leavesOfFormula (branch (.lt a b) yes no)) :
    m ∈ leavesOfFormula yes ∨ m ∈ leavesOfFormula no := by
  simpa [branch, leavesOfFormula] using hm

theorem mem_leavesOfFormula_sizeCases {p : TermPoly} {k : ℕ → Formula} {m : ℕ}
    (hm : m ∈ leavesOfFormula (sizeCases p k)) :
    ∃ n, m ∈ leavesOfFormula (k n) := by
  induction p generalizing k with
  | nil => exact ⟨0, hm⟩
  | cons a p ih =>
    rcases ih hm with ⟨n, hn⟩
    by_cases h0 : n = 0
    · subst h0
      simp only [↓reduceIte] at hn
      rcases mem_leavesOfFormula_branch_eq hn with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    · rw [if_neg h0] at hn
      exact ⟨n + 1, hn⟩

theorem mem_leavesOfFormula_leadingCases {p : TermPoly} {k : Term → Formula} {m : ℕ}
    (hm : m ∈ leavesOfFormula (leadingCases p k)) :
    ∃ t, m ∈ leavesOfFormula (k t) := by
  rcases mem_leavesOfFormula_sizeCases hm with ⟨n, hn⟩
  exact ⟨_, hn⟩

theorem mem_leavesOfFormula_pseudoDivLoopCases {q : TermPoly} {sq : ℕ} {cq : Term}
    {fuel c : ℕ} {a r : TermPoly} {k : ℕ → TermPoly → TermPoly → Formula} {m : ℕ}
    (hm : m ∈ leavesOfFormula (pseudoDivLoopCases q sq cq fuel c a r k)) :
    ∃ c' a' r', m ∈ leavesOfFormula (k c' a' r') := by
  induction fuel generalizing c a r with
  | zero => exact ⟨c, a, r, hm⟩
  | succ n ih =>
    rcases mem_leavesOfFormula_sizeCases hm with ⟨sr, hsr⟩
    by_cases hlt : sr < sq
    · rw [if_pos hlt] at hsr
      exact ⟨c, a, r, hsr⟩
    · rw [if_neg hlt] at hsr
      rcases mem_leavesOfFormula_leadingCases hsr with ⟨cr, hcr⟩
      exact ih hcr

theorem mem_leavesOfFormula_pseudoDivCases {p q : TermPoly}
    {k : ℕ → TermPoly → TermPoly → Formula} {m : ℕ}
    (hm : m ∈ leavesOfFormula (pseudoDivCases p q k)) :
    ∃ c a r, m ∈ leavesOfFormula (k c a r) := by
  rcases mem_leavesOfFormula_sizeCases hm with ⟨sq, hsq⟩
  by_cases h0 : sq = 0
  · rw [if_pos h0] at hsq
    exact ⟨0, [], p, hsq⟩
  · rw [if_neg h0] at hsq
    rcases mem_leavesOfFormula_leadingCases hsq with ⟨cq, hcq⟩
    exact mem_leavesOfFormula_pseudoDivLoopCases hcq

theorem substEx_inftyJumpBranch (f : ℕ → Formula) (sp sq : ℕ) (cp cq : Term)
    (k : ℕ → ℕ → Formula) :
    substEx f (inftyJumpBranch sp sq cp cq k) =
      inftyJumpBranch sp sq cp cq (fun dp dm => substEx f (k dp dm)) := rfl

theorem mem_leavesOfFormula_inftyJumpBranch {sp sq : ℕ} {cp cq : Term}
    {k : ℕ → ℕ → Formula} {m : ℕ}
    (hm : m ∈ leavesOfFormula (inftyJumpBranch sp sq cp cq k)) :
    ∃ dp dm : ℕ, m ∈ leavesOfFormula (k dp dm) := by
  rcases mem_leavesOfFormula_branch_lt hm with h1 | h2
  · rcases mem_leavesOfFormula_branch_lt h1 with h1a | h1b
    · exact ⟨0, 0, h1a⟩
    · exact ⟨1, 0, h1b⟩
  · rcases mem_leavesOfFormula_branch_lt h2 with h2a | h2b
    · exact ⟨0, 1, h2a⟩
    · exact ⟨0, 0, h2b⟩

abbrev ModsItem := ℕ × TermPoly × TermPoly
abbrev ModsSumState := List ModsItem × (ℕ × ℕ)

def modsQueueFuel : List ModsItem → ℕ
  | [] => 0
  | item :: rest => (item.1 + 1) + modsQueueFuel rest

def modsSumFuel (s : ModsSumState) : ℕ :=
  modsQueueFuel s.1

@[simp] theorem modsQueueFuel_nil : modsQueueFuel [] = 0 := rfl

@[simp] theorem modsQueueFuel_cons (f : ℕ) (p q : TermPoly) (rest : List ModsItem) :
    modsQueueFuel ((f, p, q) :: rest) = (f + 1) + modsQueueFuel rest := rfl

def leafModsState (s : ModsSumState) : Formula :=
  leafMarker (Encodable.encode s)

theorem primrec_leafModsState : Primrec leafModsState :=
  primrec_leafMarker.comp Primrec.encode

def modsSumStep (rec : ModsSumState → Formula) (s : ModsSumState) : Formula :=
  match s.1 with
  | [] => .truth (decide (s.2.2 < s.2.1))
  | (0, _, _) :: rest => rec (rest, s.2)
  | (n + 1, p, q) :: rest =>
      sizeCases p (fun sp =>
        if sp = 0 then rec (rest, s.2)
        else sizeCases q (fun sq =>
          if sq = 0 then rec (rest, s.2)
          else
            let cp := coefficient p (sp - 1)
            let cq := coefficient q (sq - 1)
            inftyJumpBranch sp sq cp cq (fun dp dm =>
              pseudoDivCases p q (fun c _ r =>
                let r' := nextModTermPoly cq c r
                rec ((n, q, r') :: rest, (s.2.1 + dp, s.2.2 + dm))))))

def modsSumTpl (s : ModsSumState) : Formula :=
  modsSumStep leafModsState s

def modsSumLoop (s : ModsSumState) : Formula :=
  match _h : s.1 with
  | [] => .truth (decide (s.2.2 < s.2.1))
  | (0, _, _) :: rest => modsSumLoop (rest, s.2)
  | (n + 1, p, q) :: rest =>
      sizeCases p (fun sp =>
        if sp = 0 then modsSumLoop (rest, s.2)
        else sizeCases q (fun sq =>
          if sq = 0 then modsSumLoop (rest, s.2)
          else
            let cp := coefficient p (sp - 1)
            let cq := coefficient q (sq - 1)
            inftyJumpBranch sp sq cp cq (fun dp dm =>
              pseudoDivCases p q (fun c _ r =>
                let r' := nextModTermPoly cq c r
                modsSumLoop ((n, q, r') :: rest, (s.2.1 + dp, s.2.2 + dm))))))
termination_by modsSumFuel s
decreasing_by
  all_goals
    simp [modsSumFuel, _h]

theorem modsSumLoop_eq_step (s : ModsSumState) :
    modsSumLoop s = modsSumStep modsSumLoop s := by
  conv_lhs => unfold modsSumLoop
  unfold modsSumStep
  cases h : s.1 with
  | nil => rfl
  | cons item rest =>
    rcases item with ⟨fuel, p, q⟩
    cases fuel <;> rfl

theorem substEx_modsSumStep (f : ℕ → Formula) (rec : ModsSumState → Formula) (s : ModsSumState) :
    substEx f (modsSumStep rec s) = modsSumStep (fun s' => substEx f (rec s')) s := by
  unfold modsSumStep
  cases s.1 with
  | nil => rfl
  | cons item rest =>
    rcases item with ⟨fuel, p, q⟩
    cases fuel with
    | zero => rfl
    | succ n =>
      rw [substEx_sizeCases]
      congr 1
      funext sp
      by_cases hsp : sp = 0
      · simp [hsp]
      · rw [if_neg hsp, if_neg hsp, substEx_sizeCases]
        congr 1
        funext sq
        by_cases hsq : sq = 0
        · simp [hsq]
        · rw [if_neg hsq, if_neg hsq]
          dsimp only
          simp only [substEx_inftyJumpBranch, substEx_pseudoDivCases]

theorem mem_leavesOfFormula_modsSumTpl (s : ModsSumState) (m : ℕ)
    (hm : m ∈ leavesOfFormula (modsSumTpl s)) :
    ∃ s' : ModsSumState, Encodable.decode (α := ModsSumState) m = some s' ∧
      modsSumFuel s' < modsSumFuel s := by
  cases h : s.1 with
  | nil =>
    simp [modsSumTpl, modsSumStep, h, leavesOfFormula] at hm
  | cons item rest =>
    rcases item with ⟨fuel, p, q⟩
    cases fuel with
    | zero =>
      simp only [modsSumTpl, modsSumStep, h, leafModsState, leavesOfFormula_leafMarker,
        List.mem_singleton] at hm
      subst hm
      refine ⟨(rest, s.2), Encodable.encodek _, ?_⟩
      simp [modsSumFuel, h]
    | succ n =>
      simp only [modsSumTpl, modsSumStep, h] at hm
      rcases mem_leavesOfFormula_sizeCases hm with ⟨sp, hsp⟩
      by_cases hsp0 : sp = 0
      · rw [if_pos hsp0] at hsp
        simp only [leafModsState, leavesOfFormula_leafMarker, List.mem_singleton] at hsp
        subst hsp
        refine ⟨(rest, s.2), Encodable.encodek _, ?_⟩
        simp [modsSumFuel, h]
      · rw [if_neg hsp0] at hsp
        rcases mem_leavesOfFormula_sizeCases hsp with ⟨sq, hsq⟩
        by_cases hsq0 : sq = 0
        · rw [if_pos hsq0] at hsq
          simp only [leafModsState, leavesOfFormula_leafMarker, List.mem_singleton] at hsq
          subst hsq
          refine ⟨(rest, s.2), Encodable.encodek _, ?_⟩
          simp [modsSumFuel, h]
        · rw [if_neg hsq0] at hsq
          rcases mem_leavesOfFormula_inftyJumpBranch hsq with ⟨dp, dm, hdj⟩
          rcases mem_leavesOfFormula_pseudoDivCases hdj with ⟨c, a, r, hr⟩
          simp only [leafModsState, leavesOfFormula_leafMarker, List.mem_singleton] at hr
          subst hr
          refine ⟨((n, q, nextModTermPoly (coefficient q (sq - 1)) c r) :: rest,
            (s.2.1 + dp, s.2.2 + dm)), Encodable.encodek _, ?_⟩
          simp [modsSumFuel, h]

theorem computable_ite {A B : Type*} [Primcodable A] [Primcodable B]
    {P : A → Prop} [DecidablePred P] {f g : A → B}
    (hP : Computable (fun a => decide (P a)))
    (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if P a then f a else g a) :=
  (Computable.cond hP hf hg).of_eq (fun a => by by_cases h : P a <;> simp [h])

theorem computable_branch_lt {A : Type*} [Primcodable A]
    {a b : A → Term} {yes no : A → Formula}
    (ha : Computable a) (hb : Computable b) (hyes : Computable yes) (hno : Computable no) :
    Computable (fun x => branch (.lt (a x) (b x)) (yes x) (no x)) := by
  have htest : Computable (fun x => Formula.lt (a x) (b x)) :=
    primrec_formula_lt.to_comp.comp ha hb
  exact primrec_formula_or.to_comp.comp
    (primrec_formula_and.to_comp.comp htest hyes)
    (primrec_formula_and.to_comp.comp (primrec_formula_not.to_comp.comp htest) hno)

def headItem (s : ModsSumState) : ModsItem := s.1.getD 0 (0, [], [])
def headFuel (s : ModsSumState) : ℕ := (headItem s).1
def headP (s : ModsSumState) : TermPoly := (headItem s).2.1
def headQ (s : ModsSumState) : TermPoly := (headItem s).2.2
def restQueue (s : ModsSumState) : List ModsItem := s.1.drop 1

theorem primrec_headItem : Primrec headItem :=
  (Primrec.list_getD (0, [], [])).comp Primrec.fst (Primrec.const 0)

theorem primrec_headFuel : Primrec headFuel := Primrec.fst.comp primrec_headItem
theorem primrec_headP : Primrec headP := Primrec.fst.comp (Primrec.snd.comp primrec_headItem)
theorem primrec_headQ : Primrec headQ := Primrec.snd.comp (Primrec.snd.comp primrec_headItem)
theorem primrec_restQueue : Primrec restQueue :=
  Primrec.list_drop.comp (Primrec.const 1) Primrec.fst

def nextModLeaf (dp dm : ℕ) (s : ModsSumState) (cq : Term) (c : ℕ) (r : TermPoly) : Formula :=
  leafModsState (((headFuel s - 1, headQ s, nextModTermPoly cq c r) :: restQueue s),
    (s.2.1 + dp, s.2.2 + dm))

theorem primrec_nextModLeaf (dp dm : ℕ) :
    Primrec (fun w : (ModsSumState × Term) × ℕ × TermPoly × TermPoly =>
      nextModLeaf dp dm w.1.1 w.1.2 w.2.1 w.2.2.2) := by
  let W := (ModsSumState × Term) × ℕ × TermPoly × TermPoly
  have hS : Primrec (fun w : W => w.1.1) := Primrec.fst.comp Primrec.fst
  have hCq : Primrec (fun w : W => w.1.2) := Primrec.snd.comp Primrec.fst
  have hC : Primrec (fun w : W => w.2.1) := Primrec.fst.comp Primrec.snd
  have hR : Primrec (fun w : W => w.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hNextR : Primrec (fun w : W => nextModTermPoly w.1.2 w.2.1 w.2.2.2) :=
    primrec_nextModTermPoly.comp (hCq.pair (hC.pair hR))
  have hn : Primrec (fun w : W => headFuel w.1.1 - 1) :=
    Primrec.nat_sub.comp (primrec_headFuel.comp hS) (Primrec.const 1)
  have hitem : Primrec (fun w : W =>
      (headFuel w.1.1 - 1, headQ w.1.1, nextModTermPoly w.1.2 w.2.1 w.2.2.2)) :=
    hn.pair ((primrec_headQ.comp hS).pair hNextR)
  have hqueue : Primrec (fun w : W =>
      (headFuel w.1.1 - 1, headQ w.1.1, nextModTermPoly w.1.2 w.2.1 w.2.2.2) :: restQueue w.1.1) :=
    Primrec.list_cons.comp hitem (primrec_restQueue.comp hS)
  have hacc1 : Primrec (fun w : W => w.1.1.2.1 + dp) :=
    Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp hS)) (Primrec.const dp)
  have hacc2 : Primrec (fun w : W => w.1.1.2.2 + dm) :=
    Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp hS)) (Primrec.const dm)
  exact primrec_leafModsState.comp (hqueue.pair (hacc1.pair hacc2))

def pseudoDivLeaf (dp dm : ℕ) (s : ModsSumState) (cq : Term) : Formula :=
  pseudoDivCases (headP s) (headQ s) (fun c _ r => nextModLeaf dp dm s cq c r)

theorem computable_pseudoDivLeaf_uncurried (dp dm : ℕ) :
    Computable (fun z : ModsSumState × Term => pseudoDivLeaf dp dm z.1 z.2) :=
  computable_pseudoDivCases
    (primrec_headP.comp Primrec.fst).to_comp
    (primrec_headQ.comp Primrec.fst).to_comp
    (primrec_nextModLeaf dp dm).to_comp

theorem computable_pseudoDivLeaf (dp dm : ℕ) :
    Computable₂ (pseudoDivLeaf dp dm) :=
  (computable_pseudoDivLeaf_uncurried dp dm).to₂

theorem computable_modsSumTpl : Computable modsSumTpl := by
  have hnilBranch : Computable (fun s : ModsSumState => Formula.truth (decide (s.2.2 < s.2.1))) :=
    (primrec_formula_truth.comp
      ((Primrec.nat_lt.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd)).decide)).to_comp
  have hzeroBranch : Computable (fun s : ModsSumState => leafModsState (restQueue s, s.2)) :=
    (primrec_leafModsState.comp (primrec_restQueue.pair Primrec.snd)).to_comp
  have hsuccBranch : Computable (fun s : ModsSumState =>
      sizeCases (headP s) (fun sp =>
        if sp = 0 then leafModsState (restQueue s, s.2)
        else sizeCases (headQ s) (fun sq =>
          if sq = 0 then leafModsState (restQueue s, s.2)
          else
            let cp := coefficient (headP s) (sp - 1)
            let cq := coefficient (headQ s) (sq - 1)
            inftyJumpBranch sp sq cp cq (fun dp dm =>
              pseudoDivLeaf dp dm s cq)))) := by
    refine computable_sizeCases primrec_headP.to_comp ?_
    refine computable_ite (((Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide).to_comp)
      (hzeroBranch.comp Computable.fst) ?_
    refine computable_sizeCases (primrec_headQ.comp Primrec.fst).to_comp ?_
    refine computable_ite (((Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide).to_comp)
      (hzeroBranch.comp (Computable.fst.comp Computable.fst)) ?_
    let Z := (ModsSumState × ℕ) × ℕ
    have hS : Primrec (fun z : Z => z.1.1) := Primrec.fst.comp Primrec.fst
    have hSp : Primrec (fun z : Z => z.1.2) := Primrec.snd.comp Primrec.fst
    have hSq : Primrec (fun z : Z => z.2) := Primrec.snd
    have hCp : Primrec (fun z : Z => coefficient (headP z.1.1) (z.1.2 - 1)) :=
      primrec_coefficient.comp (primrec_headP.comp hS)
        (Primrec.nat_sub.comp hSp (Primrec.const 1))
    have hCq : Primrec (fun z : Z => coefficient (headQ z.1.1) (z.2 - 1)) :=
      primrec_coefficient.comp (primrec_headQ.comp hS)
        (Primrec.nat_sub.comp hSq (Primrec.const 1))
    have hMProd : Computable (fun z : Z =>
        Term.mul (minftyTerm z.1.2 (coefficient (headP z.1.1) (z.1.2 - 1)))
          (minftyTerm z.2 (coefficient (headQ z.1.1) (z.2 - 1)))) :=
      (primrec_term_mul.comp
        (primrec_minftyTerm.comp hSp hCp)
        (primrec_minftyTerm.comp hSq hCq)).to_comp
    have hPProd : Computable (fun z : Z =>
        Term.mul (coefficient (headP z.1.1) (z.1.2 - 1))
          (coefficient (headQ z.1.1) (z.2 - 1))) :=
      (primrec_term_mul.comp hCp hCq).to_comp
    have hZero : Computable (fun _ : Z => Term.zero) := Computable.const Term.zero
    have hLeaf (dp dm : ℕ) : Computable (fun z : Z =>
        pseudoDivLeaf dp dm z.1.1 (coefficient (headQ z.1.1) (z.2 - 1))) :=
      (computable_pseudoDivLeaf dp dm).comp hS.to_comp hCq.to_comp
    exact computable_branch_lt hMProd hZero
      (computable_branch_lt hPProd hZero (hLeaf 0 0) (hLeaf 1 0))
      (computable_branch_lt hPProd hZero (hLeaf 0 1) (hLeaf 0 0))
  have hcombined : Computable (fun s : ModsSumState =>
      if s.1.length = 0 then Formula.truth (decide (s.2.2 < s.2.1))
      else if headFuel s = 0 then leafModsState (restQueue s, s.2)
      else
        sizeCases (headP s) (fun sp =>
          if sp = 0 then leafModsState (restQueue s, s.2)
          else sizeCases (headQ s) (fun sq =>
            if sq = 0 then leafModsState (restQueue s, s.2)
            else
              let cp := coefficient (headP s) (sp - 1)
              let cq := coefficient (headQ s) (sq - 1)
              inftyJumpBranch sp sq cp cq (fun dp dm =>
                pseudoDivLeaf dp dm s cq)))) := by
    have hisEmpty : Computable (fun s : ModsSumState => decide (s.1.length = 0)) :=
      ((Primrec.eq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 0)).decide).to_comp
    have hisZero : Computable (fun s : ModsSumState => decide (headFuel s = 0)) :=
      ((Primrec.eq.comp primrec_headFuel (Primrec.const 0)).decide).to_comp
    exact computable_ite hisEmpty hnilBranch
      (computable_ite hisZero hzeroBranch hsuccBranch)
  refine hcombined.of_eq (fun s => ?_)
  unfold modsSumTpl modsSumStep
  cases h : s.1 with
  | nil => simp
  | cons item rest =>
    rcases item with ⟨fuel, p, q⟩
    cases fuel <;> simp [h, headFuel, headP, headQ, headItem, restQueue, pseudoDivLeaf, nextModLeaf]

theorem computable_modsSumLoop : Computable modsSumLoop := by
  refine computable_of_leaf_template modsSumLoop modsSumFuel modsSumTpl
    computable_modsSumTpl mem_leavesOfFormula_modsSumTpl ?_
  intro s
  unfold modsSumTpl
  rw [substEx_modsSumStep]
  have hleaf : (fun s' : ModsSumState =>
      substEx (fun n => (Encodable.decode (α := ModsSumState) n).casesOn (Formula.truth false) modsSumLoop)
        (leafModsState s')) = modsSumLoop := by
    funext s'
    rw [leafModsState, substEx_leafMarker, Encodable.encodek]
  rw [hleaf, ← modsSumLoop_eq_step]

noncomputable def realModsQueueSum (ρ : ℕ → ℝ) : List ModsItem → ℤ
  | [] => 0
  | (fuel, p, q) :: rest =>
      realModsChangesAux fuel (specialize ρ p) (specialize ρ q) + realModsQueueSum ρ rest

noncomputable def realModsSumState (s : ModsSumState) (ρ : ℕ → ℝ) : ℤ :=
  ((s.2.1 : ℤ) - (s.2.2 : ℤ)) + realModsQueueSum ρ s.1

theorem holds_modsSumLoop (s : ModsSumState) (ρ : ℕ → ℝ) :
    (modsSumLoop s).Holds ρ ↔ 0 < realModsSumState s ρ := by
  induction hn : modsSumFuel s using Nat.strongRecOn generalizing s with
  | ind k ih =>
    rw [modsSumLoop_eq_step]
    unfold modsSumStep realModsSumState
    cases h : s.1 with
    | nil =>
      simp only [realModsQueueSum, add_zero, Formula.Holds, decide_eq_true_eq]
      omega
    | cons item rest =>
      rcases item with ⟨fuel, p, q⟩
      cases fuel with
      | zero =>
        have hlt : modsSumFuel (rest, s.2) < k := by
          rw [← hn]
          simp [modsSumFuel, h]
        rw [ih _ hlt (rest, s.2) rfl]
        simp [realModsSumState, realModsQueueSum, realModsChangesAux]
      | succ n =>
        rw [holds_sizeCases, ← realSize_eq_specializedSize]
        by_cases hp0 : realSize (specialize ρ p) = 0
        · rw [if_pos hp0]
          have hlt : modsSumFuel (rest, s.2) < k := by
            rw [← hn]
            simp [modsSumFuel, h]
          rw [ih _ hlt (rest, s.2) rfl]
          simp [realModsSumState, realModsQueueSum, realModsChangesAux, hp0]
        · rw [if_neg hp0, holds_sizeCases, ← realSize_eq_specializedSize]
          by_cases hq0 : realSize (specialize ρ q) = 0
          · rw [if_pos hq0]
            have hlt : modsSumFuel (rest, s.2) < k := by
              rw [← hn]
              simp [modsSumFuel, h]
            rw [ih _ hlt (rest, s.2) rfl]
            simp [realModsSumState, realModsQueueSum, realModsChangesAux, hp0, hq0]
          · rw [if_neg hq0]
            dsimp only
            let sp := realSize (specialize ρ p)
            let sq := realSize (specialize ρ q)
            let cpSel := coefficient p (sp - 1)
            let cqSel := coefficient q (sq - 1)
            have hcp : cpSel.eval ρ = (specialize ρ p).leadingCoeff :=
              eval_coefficient_of_specializedSize_ne_zero p ρ hp0
            have hcq : cqSel.eval ρ = (specialize ρ q).leadingCoeff :=
              eval_coefficient_of_specializedSize_ne_zero q ρ hq0
            rw [holds_inftyJumpBranch sp sq cpSel cqSel _ ρ (specialize ρ p) (specialize ρ q)
              (fun dj => 0 < (((s.2.1 : ℤ) - (s.2.2 : ℤ)) + dj) +
                (realModsChangesAux n (specialize ρ q)
                  (realNextMod (specialize ρ p) (specialize ρ q)) +
                  realModsQueueSum ρ rest))
              rfl rfl hcp hcq]
            · simp only [realModsQueueSum, realModsChangesAux, if_neg hp0, if_neg hq0]
              constructor <;> intro hpos <;> linarith
            · intro dp dm
              let P : ℕ → Polynomial ℝ → Polynomial ℝ → Prop := fun c _ rReal =>
                0 < (((s.2.1 : ℤ) - (s.2.2 : ℤ)) + ((dp : ℤ) - (dm : ℤ))) +
                  (realModsChangesAux n (specialize ρ q)
                    (-(Polynomial.C ((specialize ρ q).leadingCoeff ^ c) * rReal)) +
                    realModsQueueSum ρ rest)
              have hk : ∀ c a r,
                  (modsSumLoop ((n, q, nextModTermPoly cqSel c r) :: rest,
                    (s.2.1 + dp, s.2.2 + dm))).Holds ρ ↔
                  P c (specialize ρ a) (specialize ρ r) := by
                intro c a r
                have hlt : modsSumFuel
                    ((n, q, nextModTermPoly cqSel c r) :: rest, (s.2.1 + dp, s.2.2 + dm)) < k := by
                  rw [← hn]
                  simp [modsSumFuel, h]
                rw [ih _ hlt _ rfl]
                simp only [realModsSumState, realModsQueueSum, specialize_nextModTermPoly,
                  hcq, Nat.cast_add, P]
                constructor <;> intro hpos <;> linarith
              rw [holds_pseudoDivCases p q _ ρ P hk]
              dsimp only [P]
              rw [realNextMod_eq_of_fuel (specialize ρ p) (specialize ρ q) p.length
                (realSize_specialize_le_length ρ p)]

def expProducts : List TermPoly → List TermPoly
  | [] => [[Term.one]]
  | q :: qs => (expProducts qs).map (mul q) ++ (expProducts qs).map (mul (mul q q))

private def expProductsStep (q : TermPoly) (acc : List TermPoly) : List TermPoly :=
  acc.map (mul q) ++ acc.map (mul (mul q q))

private theorem expProducts_eq_foldr (sq : List TermPoly) :
    sq.foldr expProductsStep [[Term.one]] = expProducts sq := by
  induction sq with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.foldr_cons, ih, expProductsStep, expProducts]

theorem primrec_expProducts : Primrec expProducts := by
  have hmap1 : Primrec (fun p : TermPoly × List TermPoly => p.2.map (mul p.1)) :=
    Primrec.list_map Primrec.snd
      (primrec_poly_mul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have hmap2 : Primrec (fun p : TermPoly × List TermPoly => p.2.map (mul (mul p.1 p.1))) :=
    Primrec.list_map Primrec.snd
      (primrec_poly_mul.comp
        (primrec_poly_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
        Primrec.snd).to₂
  have hstep : Primrec₂ (fun (_ : List TermPoly) (p : TermPoly × List TermPoly) =>
      expProductsStep p.1 p.2) :=
    (Primrec.list_append.comp (hmap1.comp Primrec.snd) (hmap2.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const [[Term.one]]) hstep).of_eq
    expProducts_eq_foldr

theorem realSign_add_realSign_mul_self (y : ℝ) :
    realSign y + realSign (y * y) = if 0 < y then 2 else 0 := by
  rcases lt_trichotomy 0 y with hy | rfl | hy
  · rw [if_pos hy, realSign_pos hy, realSign_mul, realSign_pos hy]
    rfl
  · simp
  · have hnp : ¬ 0 < y := not_lt.mpr (le_of_lt hy)
    rw [if_neg hnp, realSign_neg hy, realSign_mul, realSign_neg hy]
    rfl

private theorem sum_map_mul_int (xs : List ℤ) (c : ℤ) :
    (xs.map (fun x => c * x)).sum = c * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

noncomputable def posWeight (sq : List TermPoly) (ρ : ℕ → ℝ) (x : ℝ) : ℤ :=
  haveI := Classical.propDecidable
  if ∀ q ∈ sq, 0 < (specialize ρ q).eval x then (2 : ℤ) ^ sq.length else 0

theorem sum_realSign_expProducts (sq : List TermPoly) (ρ : ℕ → ℝ) (x : ℝ) :
    ((expProducts sq).map (fun r => realSign ((specialize ρ r).eval x))).sum =
      posWeight sq ρ x := by
  classical
  induction sq with
  | nil =>
    simp [expProducts, posWeight, specialize, Term.eval, realSign_one]
  | cons q qs ih =>
    simp only [expProducts, List.map_append, List.sum_append]
    have h1 : (((expProducts qs).map (mul q)).map
          (fun r => realSign ((specialize ρ r).eval x))) =
        ((expProducts qs).map (fun r => realSign ((specialize ρ r).eval x))).map
          (fun s => realSign ((specialize ρ q).eval x) * s) := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left (fun r _ => ?_)
      simp [specialize_mul, Polynomial.eval_mul, realSign_mul]
    have h2 : (((expProducts qs).map (mul (mul q q))).map
          (fun r => realSign ((specialize ρ r).eval x))) =
        ((expProducts qs).map (fun r => realSign ((specialize ρ r).eval x))).map
          (fun s => realSign ((specialize ρ q).eval x * (specialize ρ q).eval x) * s) := by
      rw [List.map_map, List.map_map]
      refine List.map_congr_left (fun r _ => ?_)
      simp [specialize_mul, Polynomial.eval_mul, realSign_mul]
    rw [h1, h2, sum_map_mul_int, sum_map_mul_int, ← add_mul,
        realSign_add_realSign_mul_self, ih]
    unfold posWeight
    by_cases hq : 0 < (specialize ρ q).eval x <;>
      by_cases hqs : ∀ q' ∈ qs, 0 < (specialize ρ q').eval x <;>
      simp [hq, hqs, pow_succ']

def initModsQueue (p : TermPoly) (sq : List TermPoly) : List ModsItem :=
  (expProducts sq).map (fun r =>
    let qr := mul (deriv p) r
    (qr.length, p, qr))

theorem primrec_initModsQueue : Primrec₂ initModsQueue := by
  let Z := TermPoly × List TermPoly
  have hexp : Primrec (fun z : Z => expProducts z.2) :=
    primrec_expProducts.comp Primrec.snd
  have hqr : Primrec (fun w : Z × TermPoly => mul (deriv w.1.1) w.2) :=
    primrec_poly_mul.comp (primrec_deriv.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have helem : Primrec₂ (fun (z : Z) (r : TermPoly) =>
      let qr := mul (deriv z.1) r
      (qr.length, z.1, qr)) :=
    ((Primrec.list_length.comp hqr).pair ((Primrec.fst.comp Primrec.fst).pair hqr)).to₂
  exact (Primrec.list_map hexp helem).to₂

def ccountWeakPos (p : TermPoly) (sq : List TermPoly) : Formula :=
  modsSumLoop (initModsQueue p sq, (0, 0))

theorem computable_ccountWeakPos : Computable₂ ccountWeakPos := by
  exact (computable_modsSumLoop.comp
    (primrec_initModsQueue.to_comp.pair (Computable.const (0, 0)))).to₂

private theorem realModsQueueSum_initModsQueue (p : TermPoly) (sq : List TermPoly) (ρ : ℕ → ℝ) :
    realModsQueueSum ρ (initModsQueue p sq) =
      ((expProducts sq).map (fun r => tarskiQueryR (specialize ρ p) (specialize ρ r))).sum := by
  unfold initModsQueue
  induction expProducts sq with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, realModsQueueSum, ih, List.sum_cons]
    congr 1
    have hle : realSize (specialize ρ (mul (deriv p) r)) ≤ (mul (deriv p) r).length :=
      realSize_specialize_le_length ρ _
    rw [realModsChangesAux_eq_realChangesPoly_realMods _ _ _ hle,
        specialize_mul, specialize_deriv]
    exact realTaqR_eq_tarskiQueryR (specialize ρ p) (specialize ρ r)

private theorem list_sum_finset_sum_comm {α : Type*} (xs : List α) (S : Finset ℝ)
    (f : α → ℝ → ℤ) :
    (xs.map (fun a => ∑ x ∈ S, f a x)).sum =
      ∑ x ∈ S, (xs.map (fun a => f a x)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

theorem sum_tarskiQueryR_expProducts (p : TermPoly) (sq : List TermPoly) (ρ : ℕ → ℝ) :
    ((expProducts sq).map (fun r => tarskiQueryR (specialize ρ p) (specialize ρ r))).sum =
      ∑ x ∈ (specialize ρ p).roots.toFinset, posWeight sq ρ x := by
  unfold tarskiQueryR
  rw [list_sum_finset_sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact sum_realSign_expProducts sq ρ x

theorem posWeight_nonneg (sq : List TermPoly) (ρ : ℕ → ℝ) (x : ℝ) :
    0 ≤ posWeight sq ρ x := by
  classical
  unfold posWeight
  split_ifs
  · exact le_of_lt (pow_pos (by decide) sq.length)
  · exact le_refl 0

theorem posWeight_pos_iff (sq : List TermPoly) (ρ : ℕ → ℝ) (x : ℝ) :
    0 < posWeight sq ρ x ↔ ∀ q ∈ sq, 0 < (specialize ρ q).eval x := by
  classical
  unfold posWeight
  have hpow : (0 : ℤ) < (2 : ℤ) ^ sq.length := pow_pos (by decide) sq.length
  by_cases h : ∀ q ∈ sq, 0 < (specialize ρ q).eval x
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => hpow⟩
  · rw [if_neg h]
    exact ⟨fun h0 => False.elim (lt_irrefl 0 h0), fun h' => False.elim (h h')⟩

theorem posWeight_eq_zero_of_not (sq : List TermPoly) (ρ : ℕ → ℝ) (x : ℝ)
    (h : ¬ ∀ q ∈ sq, 0 < (specialize ρ q).eval x) :
    posWeight sq ρ x = 0 := by
  classical
  unfold posWeight
  exact if_neg h

theorem holds_ccountWeakPos_iff_roots (p : TermPoly) (sq : List TermPoly) (ρ : ℕ → ℝ) :
    (ccountWeakPos p sq).Holds ρ ↔
      ∃ x ∈ (specialize ρ p).roots.toFinset, ∀ q ∈ sq, 0 < (specialize ρ q).eval x := by
  rw [ccountWeakPos, holds_modsSumLoop]
  simp only [realModsSumState, Nat.cast_zero, sub_self, zero_add,
    realModsQueueSum_initModsQueue, sum_tarskiQueryR_expProducts]
  constructor
  · intro hpos
    by_contra hnone
    have hzero : (∑ x ∈ (specialize ρ p).roots.toFinset, posWeight sq ρ x) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      exact posWeight_eq_zero_of_not sq ρ x (fun hall => hnone ⟨x, hx, hall⟩)
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · rintro ⟨x₀, hx₀, hall₀⟩
    exact Finset.sum_pos' (fun x _ => posWeight_nonneg sq ρ x)
      ⟨x₀, hx₀, (posWeight_pos_iff sq ρ x₀).mpr hall₀⟩

theorem holds_ccountWeakPos (p : TermPoly) (sq : List TermPoly) (ρ : ℕ → ℝ) :
    (ccountWeakPos p sq).Holds ρ ↔
      specialize ρ p ≠ 0 ∧
        ∃ x : ℝ, (specialize ρ p).eval x = 0 ∧ ∀ q ∈ sq, 0 < (specialize ρ q).eval x := by
  rw [holds_ccountWeakPos_iff_roots]
  by_cases hp : specialize ρ p = 0
  · simp [hp]
  · simp only [hp, ne_eq, not_false_eq_true, true_and, Multiset.mem_toFinset,
      Polynomial.mem_roots hp, Polynomial.IsRoot]

end Grunbaum2003.FormulaCompiler.Parametric

open scoped BigOperators

namespace Grunbaum2003.FormulaCompiler.Parametric

def isQF : Formula → Bool
  | .truth _ => true
  | .eq _ _ => true
  | .lt _ _ => true
  | .le _ _ => true
  | .not p => isQF p
  | .and p q => isQF p && isQF q
  | .or p q => isQF p && isQF q
  | .all _ => false
  | .ex _ => false

theorem isQF_branch {test yes no : Formula}
    (ht : isQF test = true) (hy : isQF yes = true) (hn : isQF no = true) :
    isQF (branch test yes no) = true := by
  simp [branch, isQF, ht, hy, hn]

theorem isQF_sizeCases (p : TermPoly) (k : ℕ → Formula)
    (hk : ∀ n, isQF (k n) = true) :
    isQF (sizeCases p k) = true := by
  induction p generalizing k with
  | nil => exact hk 0
  | cons a p ih =>
    rw [sizeCases]
    refine ih _ (fun n => ?_)
    split_ifs
    · exact isQF_branch rfl (hk 0) (hk 1)
    · exact hk (n + 1)

theorem isQF_leadingCases (p : TermPoly) (k : Term → Formula)
    (hk : ∀ t, isQF (k t) = true) :
    isQF (leadingCases p k) = true :=
  isQF_sizeCases p _ (fun _ => hk _)

theorem isQF_pseudoDivLoopCases (q : TermPoly) (sq : ℕ) (cq : Term)
    (fuel c : ℕ) (a r : TermPoly) (k : ℕ → TermPoly → TermPoly → Formula)
    (hk : ∀ c' a' r', isQF (k c' a' r') = true) :
    isQF (pseudoDivLoopCases q sq cq fuel c a r k) = true := by
  induction fuel generalizing c a r with
  | zero => exact hk c a r
  | succ n ih =>
    rw [pseudoDivLoopCases]
    refine isQF_sizeCases r _ (fun sr => ?_)
    split_ifs
    · exact hk c a r
    · exact isQF_leadingCases r _ (fun _ => ih _ _ _)

theorem isQF_pseudoDivCases (p q : TermPoly)
    (k : ℕ → TermPoly → TermPoly → Formula)
    (hk : ∀ c a r, isQF (k c a r) = true) :
    isQF (pseudoDivCases p q k) = true := by
  rw [pseudoDivCases]
  refine isQF_sizeCases q _ (fun sq => ?_)
  split_ifs
  · exact hk 0 [] p
  · exact isQF_leadingCases q _ (fun cq => isQF_pseudoDivLoopCases q sq cq p.length 0 [] p k hk)

theorem isQF_inftyJumpBranch (sp sq : ℕ) (cp cq : Term)
    (k : ℕ → ℕ → Formula)
    (hk : ∀ dp dm, isQF (k dp dm) = true) :
    isQF (inftyJumpBranch sp sq cp cq k) = true :=
  isQF_branch rfl
    (isQF_branch rfl (hk 0 0) (hk 1 0))
    (isQF_branch rfl (hk 0 1) (hk 0 0))

theorem isQF_modsSumLoop (s : ModsSumState) :
    isQF (modsSumLoop s) = true := by
  induction hn : modsSumFuel s using Nat.strongRecOn generalizing s with
  | ind k ih =>
    rw [modsSumLoop_eq_step]
    unfold modsSumStep
    cases h : s.1 with
    | nil => rfl
    | cons item rest =>
      rcases item with ⟨fuel, p, q⟩
      cases fuel with
      | zero =>
        refine ih _ ?_ (rest, s.2) rfl
        rw [← hn]
        simp [modsSumFuel, h]
      | succ n =>
        refine isQF_sizeCases p _ (fun sp => ?_)
        split_ifs with hsp0
        · refine ih _ ?_ (rest, s.2) rfl
          rw [← hn]
          simp [modsSumFuel, h]
        · refine isQF_sizeCases q _ (fun sq => ?_)
          split_ifs with hsq0
          · refine ih _ ?_ (rest, s.2) rfl
            rw [← hn]
            simp [modsSumFuel, h]
          · refine isQF_inftyJumpBranch _ _ _ _ _ (fun dp dm => ?_)
            refine isQF_pseudoDivCases p q _ (fun c _ r => ?_)
            refine ih _ ?_ _ rfl
            rw [← hn]
            simp [modsSumFuel, h]

theorem isQF_ccountWeakPos (p : TermPoly) (sq : List TermPoly) :
    isQF (ccountWeakPos p sq) = true :=
  isQF_modsSumLoop _

theorem realSign_eval_of_forall_lt_root (g : Polynomial ℝ) (hg : g ≠ 0) (r : ℝ)
    (hroots : ∀ x : ℝ, g.IsRoot x → r < x) :
    realSign (g.eval r) = realSign (minftyCoeff g) := by
  let fn := g.comp (Polynomial.C (-1 : ℝ) * Polynomial.X)
  have hfn_coeff_gen : ∀ (p : Polynomial ℝ) (i : ℕ),
      (p.comp (Polynomial.C (-1 : ℝ) * Polynomial.X)).coeff i = p.coeff i * (-1 : ℝ) ^ i := by
    intro p
    refine Polynomial.induction_on' p ?_ ?_
    · intro p₁ p₂ h₁ h₂ i
      rw [Polynomial.add_comp, Polynomial.coeff_add, h₁, h₂, Polynomial.coeff_add, add_mul]
    · intro k a i
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
          Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← Polynomial.C_pow,
          ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
          Polynomial.coeff_C_mul_X_pow]
      split_ifs with h
      · subst h; rfl
      · simp
  have hfn_coeff : ∀ i : ℕ, fn.coeff i = g.coeff i * (-1 : ℝ) ^ i := hfn_coeff_gen g
  have hfn_ne : fn ≠ 0 := by
    intro h0
    have hc := hfn_coeff g.natDegree
    rw [h0, Polynomial.coeff_zero, Polynomial.coeff_natDegree] at hc
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg)
      (pow_ne_zero _ (by norm_num)) hc.symm
  have hfn_roots : ∀ x : ℝ, fn.IsRoot x → x < -r := by
    intro x hx
    rw [Polynomial.IsRoot, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, neg_one_mul] at hx
    have hlt := hroots (-x) hx
    linarith
  have hsign := realSign_eval_of_forall_root_lt fn hfn_ne (-r) hfn_roots
  have heval : fn.eval (-r) = g.eval r := by
    simp [fn, Polynomial.eval_comp]
  have hnd : fn.natDegree = g.natDegree := by
    refine le_antisymm ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro i hi
      rw [hfn_coeff i, Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
    · refine Polynomial.le_natDegree_of_ne_zero ?_
      rw [hfn_coeff g.natDegree, Polynomial.coeff_natDegree]
      exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg) (pow_ne_zero _ (by norm_num))
  have hlc_fn : fn.leadingCoeff = minftyCoeff g := by
    rw [minftyCoeff_eq_of_ne_zero g hg, Polynomial.leadingCoeff, hnd,
        hfn_coeff g.natDegree, Polynomial.coeff_natDegree, mul_comm]
  rw [← heval, hsign, hlc_fn]

theorem pos_of_realSign_eq_one {x : ℝ} (h : realSign x = 1) : 0 < x := by
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · exact hx
  · simp at h
  · rw [realSign_neg hx] at h
    omega

theorem pos_of_pos_of_no_roots_between (f : Polynomial ℝ) {x y : ℝ}
    (hx : 0 < f.eval x)
    (hno : ∀ z : ℝ, min x y ≤ z → z ≤ max x y → ¬ f.IsRoot z) :
    0 < f.eval y := by
  by_contra hle
  have hy : f.eval y ≤ 0 := not_lt.mp hle
  rcases le_total x y with hxy | hyx
  · have hcont : ContinuousOn (fun t => f.eval t) (Set.Icc x y) := f.continuous.continuousOn
    have h0 : (0 : ℝ) ∈ Set.Icc (f.eval y) (f.eval x) := ⟨hy, le_of_lt hx⟩
    obtain ⟨z, ⟨hzx, hzy⟩, hfz⟩ := intermediate_value_Icc' hxy hcont h0
    exact hno z (by rwa [min_eq_left hxy]) (by rwa [max_eq_right hxy]) hfz
  · have hcont : ContinuousOn (fun t => f.eval t) (Set.Icc y x) := f.continuous.continuousOn
    have h0 : (0 : ℝ) ∈ Set.Icc (f.eval y) (f.eval x) := ⟨hy, le_of_lt hx⟩
    obtain ⟨z, ⟨hzy, hzx⟩, hfz⟩ := intermediate_value_Icc hyx hcont h0
    exact hno z (by rwa [min_eq_right hyx]) (by rwa [max_eq_left hyx]) hfz

def sumSqPoly (sp : List TermPoly) : TermPoly :=
  sp.foldr (fun p acc => add (mul p p) acc) []

theorem primrec_sumSqPoly : Primrec sumSqPoly := by
  have hstep : Primrec₂ (fun (_ : List TermPoly) (z : TermPoly × TermPoly) =>
      add (mul z.1 z.1) z.2) :=
    (primrec_poly_add.comp
      (primrec_poly_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr Primrec.id (Primrec.const []) hstep

theorem eval_specialize_sumSqPoly_nonneg (sp : List TermPoly) (ρ : ℕ → ℝ) (x : ℝ) :
    0 ≤ (specialize ρ (sumSqPoly sp)).eval x := by
  induction sp with
  | nil => simp [sumSqPoly, specialize]
  | cons p ps ih =>
    simp only [sumSqPoly, List.foldr_cons, specialize_add, specialize_mul,
      Polynomial.eval_add, Polynomial.eval_mul]
    exact add_nonneg (mul_self_nonneg _) ih

theorem eval_specialize_sumSqPoly_eq_zero_iff (sp : List TermPoly) (ρ : ℕ → ℝ) (x : ℝ) :
    (specialize ρ (sumSqPoly sp)).eval x = 0 ↔
      ∀ p ∈ sp, (specialize ρ p).eval x = 0 := by
  induction sp with
  | nil => simp [sumSqPoly, specialize]
  | cons p ps ih =>
    have h1 : 0 ≤ (specialize ρ p).eval x * (specialize ρ p).eval x := mul_self_nonneg _
    have h2 : 0 ≤ (specialize ρ (sumSqPoly ps)).eval x :=
      eval_specialize_sumSqPoly_nonneg ps ρ x
    rw [show sumSqPoly (p :: ps) = add (mul p p) (sumSqPoly ps) from rfl]
    simp only [specialize_add, specialize_mul,
      Polynomial.eval_add, Polynomial.eval_mul, List.mem_cons]
    constructor
    · intro h0 q hq
      have hp0 : (specialize ρ p).eval x * (specialize ρ p).eval x = 0 := by linarith
      have hps0 : (specialize ρ (sumSqPoly ps)).eval x = 0 := by linarith
      rcases hq with rfl | hq
      · exact mul_self_eq_zero.mp hp0
      · exact (ih.mp hps0) q hq
    · intro hall
      have hp0 : (specialize ρ p).eval x = 0 := hall p (Or.inl rfl)
      have hps0 : (specialize ρ (sumSqPoly ps)).eval x = 0 :=
        ih.mpr (fun q hq => hall q (Or.inr hq))
      rw [hp0, mul_zero, zero_add]
      exact hps0

def prodPoly (sq : List TermPoly) : TermPoly :=
  sq.foldr mul [Term.one]

theorem primrec_prodPoly : Primrec prodPoly :=
  Primrec.list_foldr Primrec.id (Primrec.const [Term.one])
    (primrec_poly_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem eval_specialize_prodPoly_pos_of_forall_pos {sq : List TermPoly} {ρ : ℕ → ℝ} {x : ℝ}
    (h : ∀ q ∈ sq, 0 < (specialize ρ q).eval x) :
    0 < (specialize ρ (prodPoly sq)).eval x := by
  induction sq with
  | nil =>
    simp [prodPoly, specialize, Term.eval]
  | cons q qs ih =>
    rw [show prodPoly (q :: qs) = mul q (prodPoly qs) from rfl,
      specialize_mul, Polynomial.eval_mul]
    exact mul_pos (h q (List.mem_cons.mpr (Or.inl rfl)))
      (ih (fun q' hq' => h q' (List.mem_cons.mpr (Or.inr hq'))))

theorem specialize_prodPoly_ne_zero {sq : List TermPoly} {ρ : ℕ → ℝ}
    (h : ∀ q ∈ sq, specialize ρ q ≠ 0) :
    specialize ρ (prodPoly sq) ≠ 0 := by
  induction sq with
  | nil =>
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    simp [prodPoly, specialize, Term.eval] at this
  | cons q qs ih =>
    rw [show prodPoly (q :: qs) = mul q (prodPoly qs) from rfl, specialize_mul]
    exact mul_ne_zero (h q (List.mem_cons.mpr (Or.inl rfl)))
      (ih (fun q' hq' => h q' (List.mem_cons.mpr (Or.inr hq'))))

theorem isRoot_specialize_prodPoly_of_mem {sq : List TermPoly} {q : TermPoly}
    (hq : q ∈ sq) (ρ : ℕ → ℝ) {x : ℝ} (hx : (specialize ρ q).IsRoot x) :
    (specialize ρ (prodPoly sq)).IsRoot x := by
  induction sq with
  | nil => cases hq
  | cons q₀ qs ih =>
    rw [show prodPoly (q₀ :: qs) = mul q₀ (prodPoly qs) from rfl,
      specialize_mul, Polynomial.IsRoot, Polynomial.eval_mul]
    rcases List.mem_cons.mp hq with rfl | hq'
    · rw [hx.eq_zero, zero_mul]
    · rw [(ih hq').eq_zero, mul_zero]

def posAtPInftyPoly (q : TermPoly) : Formula :=
  leadingCases q (fun cq => .lt .zero cq)

theorem primrec_posAtPInftyPoly : Primrec posAtPInftyPoly :=
  primrec_leadingCases Primrec.id (primrec_formula_lt.comp (Primrec.const Term.zero) Primrec.snd)

theorem isQF_posAtPInftyPoly (q : TermPoly) : isQF (posAtPInftyPoly q) = true :=
  isQF_leadingCases q _ (fun _ => rfl)

theorem holds_posAtPInftyPoly (q : TermPoly) (ρ : ℕ → ℝ) :
    (posAtPInftyPoly q).Holds ρ ↔ 0 < (specialize ρ q).leadingCoeff :=
  holds_leading_pos q ρ

def posAtMInftyPoly (q : TermPoly) : Formula :=
  sizeCases q (fun s =>
    .lt .zero (minftyTerm s (if s = 0 then .zero else coefficient q (s - 1))))

theorem primrec_posAtMInftyPoly : Primrec posAtMInftyPoly := by
  refine primrec_sizeCases Primrec.id ?_
  have hsel : Primrec (fun z : TermPoly × ℕ =>
      if z.2 = 0 then Term.zero else coefficient z.1 (z.2 - 1)) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (Primrec.const Term.zero)
      (primrec_coefficient.comp Primrec.fst (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
  exact primrec_formula_lt.comp (Primrec.const Term.zero) (primrec_minftyTerm.comp Primrec.snd hsel)

theorem isQF_posAtMInftyPoly (q : TermPoly) : isQF (posAtMInftyPoly q) = true :=
  isQF_sizeCases q _ (fun _ => rfl)

theorem holds_posAtMInftyPoly (q : TermPoly) (ρ : ℕ → ℝ) :
    (posAtMInftyPoly q).Holds ρ ↔ 0 < minftyCoeff (specialize ρ q) := by
  rw [posAtMInftyPoly, holds_sizeCases]
  simp only [Formula.Holds, Term.eval, eval_minftyTerm, eval_leading_selected,
    realSize_eq_specializedSize, minftyCoeff]

def allPosAtPInfty (sq : List TermPoly) : Formula :=
  sq.foldr (fun q acc => .and (posAtPInftyPoly q) acc) (.truth true)

theorem primrec_allPosAtPInfty : Primrec allPosAtPInfty :=
  Primrec.list_foldr Primrec.id (Primrec.const (Formula.truth true))
    (primrec_formula_and.comp
      (primrec_posAtPInftyPoly.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem isQF_allPosAtPInfty (sq : List TermPoly) : isQF (allPosAtPInfty sq) = true := by
  induction sq with
  | nil => rfl
  | cons q qs ih =>
    rw [show allPosAtPInfty (q :: qs) = .and (posAtPInftyPoly q) (allPosAtPInfty qs) from rfl]
    simp [isQF, isQF_posAtPInftyPoly, ih]

theorem holds_allPosAtPInfty (sq : List TermPoly) (ρ : ℕ → ℝ) :
    (allPosAtPInfty sq).Holds ρ ↔ ∀ q ∈ sq, 0 < (specialize ρ q).leadingCoeff := by
  induction sq with
  | nil => simp [allPosAtPInfty, Formula.Holds]
  | cons q qs ih =>
    rw [show allPosAtPInfty (q :: qs) = .and (posAtPInftyPoly q) (allPosAtPInfty qs) from rfl]
    simp [Formula.Holds, holds_posAtPInftyPoly, ih]

def allPosAtMInfty (sq : List TermPoly) : Formula :=
  sq.foldr (fun q acc => .and (posAtMInftyPoly q) acc) (.truth true)

theorem primrec_allPosAtMInfty : Primrec allPosAtMInfty :=
  Primrec.list_foldr Primrec.id (Primrec.const (Formula.truth true))
    (primrec_formula_and.comp
      (primrec_posAtMInftyPoly.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem isQF_allPosAtMInfty (sq : List TermPoly) : isQF (allPosAtMInfty sq) = true := by
  induction sq with
  | nil => rfl
  | cons q qs ih =>
    rw [show allPosAtMInfty (q :: qs) = .and (posAtMInftyPoly q) (allPosAtMInfty qs) from rfl]
    simp [isQF, isQF_posAtMInftyPoly, ih]

theorem holds_allPosAtMInfty (sq : List TermPoly) (ρ : ℕ → ℝ) :
    (allPosAtMInfty sq).Holds ρ ↔ ∀ q ∈ sq, 0 < minftyCoeff (specialize ρ q) := by
  induction sq with
  | nil => simp [allPosAtMInfty, Formula.Holds]
  | cons q qs ih =>
    rw [show allPosAtMInfty (q :: qs) = .and (posAtMInftyPoly q) (allPosAtMInfty qs) from rfl]
    simp [Formula.Holds, holds_posAtMInftyPoly, ih]

def existPosAll (sq : List TermPoly) : Formula :=
  .or (allPosAtPInfty sq)
    (.or (allPosAtMInfty sq)
      (ccountWeakPos (deriv (prodPoly sq)) sq))

theorem computable_existPosAll : Computable existPosAll := by
  have hc : Computable (fun sq : List TermPoly => ccountWeakPos (deriv (prodPoly sq)) sq) :=
    computable_ccountWeakPos.comp
      (primrec_deriv.comp primrec_prodPoly).to_comp
      Computable.id
  exact primrec_formula_or.to_comp.comp
    primrec_allPosAtPInfty.to_comp
    (primrec_formula_or.to_comp.comp primrec_allPosAtMInfty.to_comp hc)

theorem isQF_existPosAll (sq : List TermPoly) : isQF (existPosAll sq) = true := by
  simp [existPosAll, isQF, isQF_allPosAtPInfty, isQF_allPosAtMInfty, isQF_ccountWeakPos]

theorem holds_existPosAll (sq : List TermPoly) (ρ : ℕ → ℝ) :
    (existPosAll sq).Holds ρ ↔ ∃ x : ℝ, ∀ q ∈ sq, 0 < (specialize ρ q).eval x := by
  classical
  rw [existPosAll]
  simp only [Formula.Holds, holds_allPosAtPInfty, holds_allPosAtMInfty, holds_ccountWeakPos,
    specialize_deriv]
  let G : Polynomial ℝ := specialize ρ (prodPoly sq)
  constructor
  · rintro (hP | hM | ⟨_, x, _, hx⟩)
    · have hG_ne : G ≠ 0 := by
        refine specialize_prodPoly_ne_zero (fun q hq h0 => ?_)
        have := hP q hq
        rw [h0, Polynomial.leadingCoeff_zero] at this
        exact lt_irrefl 0 this
      let R : ℝ := if hne : G.roots.toFinset.Nonempty then G.roots.toFinset.max' hne + 1 else 0
      refine ⟨R, fun q hq => ?_⟩
      have hq_pos : 0 < (specialize ρ q).leadingCoeff := hP q hq
      have hq_ne : specialize ρ q ≠ 0 := by
        intro h0
        rw [h0, Polynomial.leadingCoeff_zero] at hq_pos
        exact lt_irrefl 0 hq_pos
      have hroots_lt : ∀ x : ℝ, (specialize ρ q).IsRoot x → x < R := by
        intro x hx
        have hxG : G.IsRoot x := isRoot_specialize_prodPoly_of_mem hq ρ hx
        have hmem : x ∈ G.roots.toFinset :=
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hG_ne).mpr hxG)
        have hne : G.roots.toFinset.Nonempty := ⟨x, hmem⟩
        have hle : x ≤ G.roots.toFinset.max' hne := Finset.le_max' _ x hmem
        dsimp only [R]
        rw [dif_pos hne]
        linarith
      have hsign := realSign_eval_of_forall_root_lt (specialize ρ q) hq_ne R hroots_lt
      rw [realSign_pos hq_pos] at hsign
      exact pos_of_realSign_eq_one hsign
    · have hG_ne : G ≠ 0 := by
        refine specialize_prodPoly_ne_zero (fun q hq h0 => ?_)
        have := hM q hq
        rw [h0, minftyCoeff_zero] at this
        exact lt_irrefl 0 this
      let L : ℝ := if hne : G.roots.toFinset.Nonempty then G.roots.toFinset.min' hne - 1 else 0
      refine ⟨L, fun q hq => ?_⟩
      have hq_pos : 0 < minftyCoeff (specialize ρ q) := hM q hq
      have hq_ne : specialize ρ q ≠ 0 := by
        intro h0
        rw [h0, minftyCoeff_zero] at hq_pos
        exact lt_irrefl 0 hq_pos
      have hroots_gt : ∀ x : ℝ, (specialize ρ q).IsRoot x → L < x := by
        intro x hx
        have hxG : G.IsRoot x := isRoot_specialize_prodPoly_of_mem hq ρ hx
        have hmem : x ∈ G.roots.toFinset :=
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hG_ne).mpr hxG)
        have hne : G.roots.toFinset.Nonempty := ⟨x, hmem⟩
        have hge : G.roots.toFinset.min' hne ≤ x := Finset.min'_le _ x hmem
        dsimp only [L]
        rw [dif_pos hne]
        linarith
      have hsign := realSign_eval_of_forall_lt_root (specialize ρ q) hq_ne L hroots_gt
      rw [realSign_pos hq_pos] at hsign
      exact pos_of_realSign_eq_one hsign
    · exact ⟨x, hx⟩
  · rintro ⟨x₀, hx₀⟩
    have hGx₀ : 0 < G.eval x₀ := eval_specialize_prodPoly_pos_of_forall_pos hx₀
    have hG_ne : G ≠ 0 := by
      intro h0
      rw [h0, Polynomial.eval_zero] at hGx₀
      exact lt_irrefl 0 hGx₀
    let RightRoots : Finset ℝ := G.roots.toFinset.filter (fun r => x₀ < r)
    let LeftRoots : Finset ℝ := G.roots.toFinset.filter (fun r => r < x₀)
    by_cases hR : RightRoots.Nonempty
    · by_cases hL : LeftRoots.Nonempty
      · right; right
        let a := LeftRoots.max' hL
        let b := RightRoots.min' hR
        have ha_mem : a ∈ LeftRoots := Finset.max'_mem _ hL
        have hb_mem : b ∈ RightRoots := Finset.min'_mem _ hR
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hG_ne] at ha_mem hb_mem
        have ha_lt : a < x₀ := ha_mem.2
        have hb_gt : x₀ < b := hb_mem.2
        have hab : a < b := lt_trans ha_lt hb_gt
        have ha_eval : G.eval a = 0 := ha_mem.1
        have hb_eval : G.eval b = 0 := hb_mem.1
        have hG'_ne : G.derivative ≠ 0 := by
          intro h0
          have hC := Polynomial.eq_C_of_derivative_eq_zero h0
          have heq : G.eval x₀ = G.eval a := by
            conv_lhs => rw [hC]
            conv_rhs => rw [hC]
            simp
          linarith
        obtain ⟨c, hc_mem, hc_deriv⟩ :=
          exists_deriv_eq_zero hab G.continuousOn (ha_eval.trans hb_eval.symm)
        rw [G.deriv] at hc_deriv
        refine ⟨hG'_ne, c, hc_deriv, fun q hq => ?_⟩
        refine pos_of_pos_of_no_roots_between (specialize ρ q) (hx₀ q hq) ?_
        intro z hz_min hz_max hqz
        have hGz : G.IsRoot z := isRoot_specialize_prodPoly_of_mem hq ρ hqz
        have hz_roots : z ∈ G.roots.toFinset :=
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hG_ne).mpr hGz)
        have hza : a < z := by
          have : a < min x₀ c := lt_min ha_lt hc_mem.1
          linarith
        have hzb : z < b := by
          have : max x₀ c < b := max_lt hb_gt hc_mem.2
          linarith
        rcases lt_trichotomy z x₀ with hzx | rfl | hxz
        · have hzL : z ∈ LeftRoots := Finset.mem_filter.mpr ⟨hz_roots, hzx⟩
          have : z ≤ a := Finset.le_max' _ z hzL
          linarith
        · have : G.eval z = 0 := hGz
          linarith
        · have hzR : z ∈ RightRoots := Finset.mem_filter.mpr ⟨hz_roots, hxz⟩
          have : b ≤ z := Finset.min'_le _ z hzR
          linarith
      · right; left
        intro q hq
        have hqx₀ : 0 < (specialize ρ q).eval x₀ := hx₀ q hq
        have hq_ne : specialize ρ q ≠ 0 := by
          intro h0
          rw [h0, Polynomial.eval_zero] at hqx₀
          exact lt_irrefl 0 hqx₀
        have hroots_gt : ∀ x : ℝ, (specialize ρ q).IsRoot x → x₀ < x := by
          intro x hx
          have hxG : G.IsRoot x := isRoot_specialize_prodPoly_of_mem hq ρ hx
          have hmem : x ∈ G.roots.toFinset :=
            Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hG_ne).mpr hxG)
          rcases lt_trichotomy x x₀ with hlt | rfl | hgt
          · exfalso
            exact hL ⟨x, Finset.mem_filter.mpr ⟨hmem, hlt⟩⟩
          · exfalso
            have : G.eval x = 0 := hxG
            linarith
          · exact hgt
        have hsign := (realSign_eval_of_forall_lt_root (specialize ρ q) hq_ne x₀ hroots_gt).symm
        rw [realSign_pos hqx₀] at hsign
        exact pos_of_realSign_eq_one hsign
    · left
      intro q hq
      have hqx₀ : 0 < (specialize ρ q).eval x₀ := hx₀ q hq
      have hq_ne : specialize ρ q ≠ 0 := by
        intro h0
        rw [h0, Polynomial.eval_zero] at hqx₀
        exact lt_irrefl 0 hqx₀
      have hroots_lt : ∀ x : ℝ, (specialize ρ q).IsRoot x → x < x₀ := by
        intro x hx
        have hxG : G.IsRoot x := isRoot_specialize_prodPoly_of_mem hq ρ hx
        have hmem : x ∈ G.roots.toFinset :=
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hG_ne).mpr hxG)
        rcases lt_trichotomy x x₀ with hlt | rfl | hgt
        · exact hlt
        · exfalso
          have : G.eval x = 0 := hxG
          linarith
        · exfalso
          exact hR ⟨x, Finset.mem_filter.mpr ⟨hmem, hgt⟩⟩
      have hsign := (realSign_eval_of_forall_root_lt (specialize ρ q) hq_ne x₀ hroots_lt).symm
      rw [realSign_pos hqx₀] at hsign
      exact pos_of_realSign_eq_one hsign

def ccountGt0 (sp sq : List TermPoly) : Formula :=
  let p := sumSqPoly sp
  sizeCases p (fun s =>
    if s = 0 then existPosAll sq
    else ccountWeakPos p sq)

theorem computable_ccountGt0_uncurried :
    Computable (fun z : List TermPoly × List TermPoly => ccountGt0 z.1 z.2) := by
  let Z := List TermPoly × List TermPoly
  have hp : Computable (fun z : Z => sumSqPoly z.1) :=
    (primrec_sumSqPoly.comp Primrec.fst).to_comp
  refine computable_sizeCases hp ?_
  have hcond : Computable (fun w : Z × ℕ => decide (w.2 = 0)) :=
    ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide).to_comp
  have hyes : Computable (fun w : Z × ℕ => existPosAll w.1.2) :=
    computable_existPosAll.comp (Computable.snd.comp Computable.fst)
  have hno : Computable (fun w : Z × ℕ => ccountWeakPos (sumSqPoly w.1.1) w.1.2) :=
    computable_ccountWeakPos.comp
      (hp.comp Computable.fst)
      (Computable.snd.comp Computable.fst)
  exact computable_ite hcond hyes hno

theorem computable_ccountGt0 : Computable₂ ccountGt0 :=
  computable_ccountGt0_uncurried.to₂

theorem isQF_ccountGt0 (sp sq : List TermPoly) : isQF (ccountGt0 sp sq) = true := by
  rw [ccountGt0]
  refine isQF_sizeCases _ _ (fun s => ?_)
  split_ifs
  · exact isQF_existPosAll sq
  · exact isQF_ccountWeakPos _ sq

theorem holds_ccountGt0 (sp sq : List TermPoly) (ρ : ℕ → ℝ) :
    (ccountGt0 sp sq).Holds ρ ↔
      ∃ x : ℝ, (∀ p ∈ sp, (specialize ρ p).eval x = 0) ∧
        (∀ q ∈ sq, 0 < (specialize ρ q).eval x) := by
  rw [ccountGt0, holds_sizeCases, ← realSize_eq_specializedSize]
  by_cases hs : realSize (specialize ρ (sumSqPoly sp)) = 0
  · rw [if_pos hs, holds_existPosAll]
    have hp0 : specialize ρ (sumSqPoly sp) = 0 := (realSize_eq_zero_iff _).mp hs
    have hall0 : ∀ x : ℝ, ∀ p ∈ sp, (specialize ρ p).eval x = 0 := by
      intro x
      rw [← eval_specialize_sumSqPoly_eq_zero_iff, hp0, Polynomial.eval_zero]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, hall0 x, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
  · rw [if_neg hs, holds_ccountWeakPos]
    have hp_ne : specialize ρ (sumSqPoly sp) ≠ 0 := (realSize_eq_zero_iff _).not.mp hs
    simp only [hp_ne, ne_eq, not_false_eq_true, true_and,
      eval_specialize_sumSqPoly_eq_zero_iff]

abbrev Clause := List Term × List Term
abbrev DNF := List Clause

def clauseHolds (c : Clause) (ρ : ℕ → ℝ) : Prop :=
  (∀ t ∈ c.1, t.eval ρ = 0) ∧ (∀ t ∈ c.2, 0 < t.eval ρ)

def dnfHolds (d : DNF) (ρ : ℕ → ℝ) : Prop :=
  ∃ c ∈ d, clauseHolds c ρ

@[simp] theorem dnfHolds_nil (ρ : ℕ → ℝ) : ¬ dnfHolds [] ρ := by
  simp [dnfHolds]

theorem dnfHolds_append (d1 d2 : DNF) (ρ : ℕ → ℝ) :
    dnfHolds (d1 ++ d2) ρ ↔ dnfHolds d1 ρ ∨ dnfHolds d2 ρ := by
  simp only [dnfHolds, List.mem_append]
  exact ⟨fun ⟨c, hc, h⟩ => hc.elim (fun h1 => Or.inl ⟨c, h1, h⟩) (fun h2 => Or.inr ⟨c, h2, h⟩),
    fun h => h.elim (fun ⟨c, hc, h⟩ => ⟨c, Or.inl hc, h⟩) (fun ⟨c, hc, h⟩ => ⟨c, Or.inr hc, h⟩)⟩

def appendClause (c1 c2 : Clause) : Clause :=
  (c1.1 ++ c2.1, c1.2 ++ c2.2)

theorem primrec_appendClause : Primrec₂ appendClause :=
  ((Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

theorem clauseHolds_appendClause (c1 c2 : Clause) (ρ : ℕ → ℝ) :
    clauseHolds (appendClause c1 c2) ρ ↔ clauseHolds c1 ρ ∧ clauseHolds c2 ρ := by
  simp only [clauseHolds, appendClause, List.mem_append]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun t ht => h1 t (Or.inl ht), fun t ht => h2 t (Or.inl ht)⟩,
      ⟨fun t ht => h1 t (Or.inr ht), fun t ht => h2 t (Or.inr ht)⟩⟩
  · rintro ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩
    exact ⟨fun t ht => ht.elim (h1a t) (h2a t), fun t ht => ht.elim (h1b t) (h2b t)⟩

def dnfAnd (d1 d2 : DNF) : DNF :=
  d1.foldr (fun c1 acc => d2.map (appendClause c1) ++ acc) []

theorem primrec_dnfAnd : Primrec₂ dnfAnd := by
  let Z := DNF × DNF
  have hmap : Primrec (fun w : Z × Clause × DNF => w.1.2.map (appendClause w.2.1)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (primrec_appendClause.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂
  have hstep : Primrec₂ (fun (z : Z) (p : Clause × DNF) => z.2.map (appendClause p.1) ++ p.2) :=
    (Primrec.list_append.comp hmap (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.fst (Primrec.const []) hstep).to₂

theorem dnfHolds_map_appendClause (c1 : Clause) (d2 : DNF) (ρ : ℕ → ℝ) :
    dnfHolds (d2.map (appendClause c1)) ρ ↔ clauseHolds c1 ρ ∧ dnfHolds d2 ρ := by
  simp only [dnfHolds, List.mem_map]
  constructor
  · rintro ⟨_, ⟨c2, hc2, rfl⟩, h⟩
    rw [clauseHolds_appendClause] at h
    exact ⟨h.1, c2, hc2, h.2⟩
  · rintro ⟨hc1, c2, hc2, hc2h⟩
    exact ⟨appendClause c1 c2, ⟨c2, hc2, rfl⟩, (clauseHolds_appendClause c1 c2 ρ).mpr ⟨hc1, hc2h⟩⟩

@[simp] theorem clauseHolds_mk (eqs pos : List Term) (ρ : ℕ → ℝ) :
    clauseHolds (eqs, pos) ρ ↔ (∀ t ∈ eqs, t.eval ρ = 0) ∧ (∀ t ∈ pos, 0 < t.eval ρ) :=
  Iff.rfl

@[simp] theorem dnfHolds_cons (c : Clause) (d : DNF) (ρ : ℕ → ℝ) :
    dnfHolds (c :: d) ρ ↔ clauseHolds c ρ ∨ dnfHolds d ρ := by
  simp [dnfHolds, exists_eq_or_imp]

theorem dnfHolds_dnfAnd (d1 d2 : DNF) (ρ : ℕ → ℝ) :
    dnfHolds (dnfAnd d1 d2) ρ ↔ dnfHolds d1 ρ ∧ dnfHolds d2 ρ := by
  induction d1 with
  | nil => simp [dnfAnd]
  | cons c1 d1 ih =>
    rw [show dnfAnd (c1 :: d1) d2 = d2.map (appendClause c1) ++ dnfAnd d1 d2 from rfl,
      dnfHolds_append, dnfHolds_map_appendClause, ih, dnfHolds_cons, or_and_right]

def subTerm (a b : Term) : Term :=
  .add a (.neg b)

theorem primrec_subTerm : Primrec₂ subTerm :=
  (primrec_term_add.comp Primrec.fst (primrec_term_neg.comp Primrec.snd)).to₂

@[simp] theorem eval_subTerm (a b : Term) (ρ : ℕ → ℝ) :
    (subTerm a b).eval ρ = a.eval ρ - b.eval ρ := by
  simp [subTerm, Term.eval, sub_eq_add_neg]

def dnfTruth (b : Bool) : DNF × DNF :=
  if b then ([([], [])], []) else ([], [([], [])])

def dnfEq (a b : Term) : DNF × DNF :=
  ([([subTerm a b], [])], [([], [subTerm b a]), ([], [subTerm a b])])

def dnfLt (a b : Term) : DNF × DNF :=
  ([([], [subTerm b a])], [([subTerm a b], []), ([], [subTerm a b])])

def dnfLe (a b : Term) : DNF × DNF :=
  ([([subTerm a b], []), ([], [subTerm b a])], [([], [subTerm a b])])

def dnfPair : Formula → DNF × DNF
  | .truth b => dnfTruth b
  | .eq a b => dnfEq a b
  | .lt a b => dnfLt a b
  | .le a b => dnfLe a b
  | .not p => ((dnfPair p).2, (dnfPair p).1)
  | .and p q => (dnfAnd (dnfPair p).1 (dnfPair q).1, (dnfPair p).2 ++ (dnfPair q).2)
  | .or p q => ((dnfPair p).1 ++ (dnfPair q).1, dnfAnd (dnfPair p).2 (dnfPair q).2)
  | .all _ => ([], [])
  | .ex _ => ([], [])

def dnfRecSpec : FormulaRecSpec Unit (DNF × DNF) where
  defaultF := ([], [])
  fTruth := fun _ b => dnfTruth b
  fEq := fun _ a b => dnfEq a b
  fLt := fun _ a b => dnfLt a b
  fLe := fun _ a b => dnfLe a b
  fNot := fun _ r => (r.2, r.1)
  fAnd := fun _ r1 r2 => (dnfAnd r1.1 r2.1, r1.2 ++ r2.2)
  fOr := fun _ r1 r2 => (r1.1 ++ r2.1, dnfAnd r1.2 r2.2)
  fAll := fun _ _ => ([], [])
  fEx := fun _ _ => ([], [])

theorem dnfPair_eq_rec (p : Formula) :
    dnfPair p = evalFormulaRec dnfRecSpec () p := by
  induction p <;> simp_all [dnfPair, evalFormulaRec, dnfRecSpec]

theorem primrec_dnfPair : Primrec dnfPair := by
  have hTruth : Primrec (fun z : Unit × Bool => dnfTruth z.2) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const true))
      (Primrec.const ([([], [])], []))
      (Primrec.const ([], [([], [])]))
  have hSubAB : Primrec (fun z : Unit × Term × Term => subTerm z.2.1 z.2.2) :=
    primrec_subTerm.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hSubBA : Primrec (fun z : Unit × Term × Term => subTerm z.2.2 z.2.1) :=
    primrec_subTerm.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  have hEq : Primrec (fun z : Unit × Term × Term => dnfEq z.2.1 z.2.2) := by
    have hc1 : Primrec (fun z : Unit × Term × Term => ([subTerm z.2.1 z.2.2], ([] : List Term))) :=
      (Primrec.list_cons.comp hSubAB (Primrec.const [])).pair (Primrec.const [])
    have hc2 : Primrec (fun z : Unit × Term × Term => (([] : List Term), [subTerm z.2.2 z.2.1])) :=
      (Primrec.const []).pair (Primrec.list_cons.comp hSubBA (Primrec.const []))
    have hc3 : Primrec (fun z : Unit × Term × Term => (([] : List Term), [subTerm z.2.1 z.2.2])) :=
      (Primrec.const []).pair (Primrec.list_cons.comp hSubAB (Primrec.const []))
    exact (Primrec.list_cons.comp hc1 (Primrec.const [])).pair
      (Primrec.list_cons.comp hc2 (Primrec.list_cons.comp hc3 (Primrec.const [])))
  have hLt : Primrec (fun z : Unit × Term × Term => dnfLt z.2.1 z.2.2) := by
    have hc1 : Primrec (fun z : Unit × Term × Term => (([] : List Term), [subTerm z.2.2 z.2.1])) :=
      (Primrec.const []).pair (Primrec.list_cons.comp hSubBA (Primrec.const []))
    have hc2 : Primrec (fun z : Unit × Term × Term => ([subTerm z.2.1 z.2.2], ([] : List Term))) :=
      (Primrec.list_cons.comp hSubAB (Primrec.const [])).pair (Primrec.const [])
    have hc3 : Primrec (fun z : Unit × Term × Term => (([] : List Term), [subTerm z.2.1 z.2.2])) :=
      (Primrec.const []).pair (Primrec.list_cons.comp hSubAB (Primrec.const []))
    exact (Primrec.list_cons.comp hc1 (Primrec.const [])).pair
      (Primrec.list_cons.comp hc2 (Primrec.list_cons.comp hc3 (Primrec.const [])))
  have hLe : Primrec (fun z : Unit × Term × Term => dnfLe z.2.1 z.2.2) := by
    have hc1 : Primrec (fun z : Unit × Term × Term => ([subTerm z.2.1 z.2.2], ([] : List Term))) :=
      (Primrec.list_cons.comp hSubAB (Primrec.const [])).pair (Primrec.const [])
    have hc2 : Primrec (fun z : Unit × Term × Term => (([] : List Term), [subTerm z.2.2 z.2.1])) :=
      (Primrec.const []).pair (Primrec.list_cons.comp hSubBA (Primrec.const []))
    have hc3 : Primrec (fun z : Unit × Term × Term => (([] : List Term), [subTerm z.2.1 z.2.2])) :=
      (Primrec.const []).pair (Primrec.list_cons.comp hSubAB (Primrec.const []))
    exact (Primrec.list_cons.comp hc1 (Primrec.list_cons.comp hc2 (Primrec.const []))).pair
      (Primrec.list_cons.comp hc3 (Primrec.const []))
  have hNot : Primrec (fun z : Unit × (DNF × DNF) => (z.2.2, z.2.1)) :=
    (Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd)
  have hR1_1 : Primrec (fun z : Unit × (DNF × DNF) × (DNF × DNF) => z.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hR1_2 : Primrec (fun z : Unit × (DNF × DNF) × (DNF × DNF) => z.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hR2_1 : Primrec (fun z : Unit × (DNF × DNF) × (DNF × DNF) => z.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hR2_2 : Primrec (fun z : Unit × (DNF × DNF) × (DNF × DNF) => z.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hAnd : Primrec (fun z : Unit × (DNF × DNF) × (DNF × DNF) =>
      (dnfAnd z.2.1.1 z.2.2.1, z.2.1.2 ++ z.2.2.2)) :=
    (primrec_dnfAnd.comp hR1_1 hR2_1).pair (Primrec.list_append.comp hR1_2 hR2_2)
  have hOr : Primrec (fun z : Unit × (DNF × DNF) × (DNF × DNF) =>
      (z.2.1.1 ++ z.2.2.1, dnfAnd z.2.1.2 z.2.2.2)) :=
    (Primrec.list_append.comp hR1_1 hR2_1).pair (primrec_dnfAnd.comp hR1_2 hR2_2)
  have hrec : Primrec (fun p : Formula => evalFormulaRec dnfRecSpec () p) :=
    primrec_evalFormulaRec (spec := dnfRecSpec) (Primrec.const ()) Primrec.id
      hTruth hEq hLt hLe hNot hAnd hOr (Primrec.const ([], [])) (Primrec.const ([], []))
  exact hrec.of_eq (fun p => (dnfPair_eq_rec p).symm)

theorem dnfHolds_dnfPair_of_isQF {p : Formula} (hp : isQF p = true) (ρ : ℕ → ℝ) :
    (dnfHolds (dnfPair p).1 ρ ↔ p.Holds ρ) ∧
      (dnfHolds (dnfPair p).2 ρ ↔ ¬ p.Holds ρ) := by
  induction p with
  | truth b =>
    cases b <;> simp [dnfPair, dnfTruth, Formula.Holds]
  | eq a b =>
    simp [dnfPair, dnfEq, Formula.Holds, sub_eq_zero, sub_pos]
  | lt a b =>
    simp [dnfPair, dnfLt, Formula.Holds, sub_eq_zero, sub_pos]
    rw [le_iff_eq_or_lt, eq_comm]
  | le a b =>
    simp [dnfPair, dnfLe, Formula.Holds, sub_eq_zero, sub_pos]
    rw [le_iff_eq_or_lt]
  | not q ih =>
    simp only [isQF] at hp
    rcases ih hp with ⟨ih1, ih2⟩
    simp [dnfPair, Formula.Holds, ih1, ih2]
  | and q r ihq ihr =>
    simp only [isQF, Bool.and_eq_true] at hp
    rcases ihq hp.1 with ⟨ihq1, ihq2⟩
    rcases ihr hp.2 with ⟨ihr1, ihr2⟩
    simp [dnfPair, dnfHolds_dnfAnd, dnfHolds_append, Formula.Holds,
      ihq1, ihq2, ihr1, ihr2]
    tauto
  | or q r ihq ihr =>
    simp only [isQF, Bool.and_eq_true] at hp
    rcases ihq hp.1 with ⟨ihq1, ihq2⟩
    rcases ihr hp.2 with ⟨ihr1, ihr2⟩
    simp [dnfPair, dnfHolds_dnfAnd, dnfHolds_append, Formula.Holds,
      ihq1, ihq2, ihr1, ihr2, not_or]
  | all _ => cases hp
  | ex _ => cases hp

def elimClause0 (c : Clause) : Formula :=
  ccountGt0 (c.1.map abstract0) (c.2.map abstract0)

theorem computable_elimClause0 : Computable elimClause0 := by
  have h1 : Primrec (fun c : Clause => c.1.map abstract0) :=
    Primrec.list_map Primrec.fst (primrec_abstract0.comp Primrec.snd).to₂
  have h2 : Primrec (fun c : Clause => c.2.map abstract0) :=
    Primrec.list_map Primrec.snd (primrec_abstract0.comp Primrec.snd).to₂
  exact computable_ccountGt0.comp h1.to_comp h2.to_comp

theorem isQF_elimClause0 (c : Clause) : isQF (elimClause0 c) = true :=
  isQF_ccountGt0 _ _

theorem holds_elimClause0 (c : Clause) (ρ : ℕ → ℝ) :
    (elimClause0 c).Holds ρ ↔ ∃ x : ℝ, clauseHolds c (consEnv x ρ) := by
  rw [elimClause0, holds_ccountGt0]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    eval_specialize_abstract0, clauseHolds]

def orFormulaList (fs : List Formula) : Formula :=
  fs.foldr Formula.or (.truth false)

theorem primrec_orFormulaList : Primrec orFormulaList :=
  Primrec.list_foldr Primrec.id (Primrec.const (Formula.truth false))
    (primrec_formula_or.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem isQF_orFormulaList (fs : List Formula) (h : ∀ f ∈ fs, isQF f = true) :
    isQF (orFormulaList fs) = true := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [show orFormulaList (f :: fs) = .or f (orFormulaList fs) from rfl]
    simp [isQF, h f (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun g hg => h g (List.mem_cons.mpr (Or.inr hg)))]

theorem holds_orFormulaList (fs : List Formula) (ρ : ℕ → ℝ) :
    (orFormulaList fs).Holds ρ ↔ ∃ f ∈ fs, f.Holds ρ := by
  induction fs with
  | nil => simp [orFormulaList, Formula.Holds]
  | cons f fs ih =>
    rw [show orFormulaList (f :: fs) = .or f (orFormulaList fs) from rfl]
    simp [Formula.Holds, ih]

def elimExQF (p : Formula) : Formula :=
  orFormulaList (((dnfPair p).1).map elimClause0)

theorem computable_elimExQF : Computable elimExQF := by
  have hd : Computable (fun p : Formula => (dnfPair p).1) :=
    (Primrec.fst.comp primrec_dnfPair).to_comp
  have hmap : Computable (fun p : Formula => ((dnfPair p).1).map elimClause0) :=
    computable_list_map hd (computable_elimClause0.comp Computable.snd).to₂
  exact primrec_orFormulaList.to_comp.comp hmap

theorem isQF_elimExQF (p : Formula) : isQF (elimExQF p) = true := by
  apply isQF_orFormulaList
  intro f hf
  rcases List.mem_map.mp hf with ⟨c, _, rfl⟩
  exact isQF_elimClause0 c

theorem holds_elimExQF {p : Formula} (hp : isQF p = true) (ρ : ℕ → ℝ) :
    (elimExQF p).Holds ρ ↔ ∃ x : ℝ, p.Holds (consEnv x ρ) := by
  rw [elimExQF, holds_orFormulaList]
  simp only [List.mem_map, exists_exists_and_eq_and, holds_elimClause0]
  constructor
  · rintro ⟨c, hc, x, hcx⟩
    exact ⟨x, (dnfHolds_dnfPair_of_isQF hp (consEnv x ρ)).1.mp ⟨c, hc, hcx⟩⟩
  · rintro ⟨x, hx⟩
    rcases (dnfHolds_dnfPair_of_isQF hp (consEnv x ρ)).1.mpr hx with ⟨c, hc, hcx⟩
    exact ⟨c, hc, x, hcx⟩

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003.FormulaCompiler.Parametric

open Grunbaum2003.FormulaCompiler

def elimFormula : Formula → Formula
  | .truth b => .truth b
  | .eq a b => .eq a b
  | .lt a b => .lt a b
  | .le a b => .le a b
  | .not p => .not (elimFormula p)
  | .and p q => .and (elimFormula p) (elimFormula q)
  | .or p q => .or (elimFormula p) (elimFormula q)
  | .all p => .not (elimExQF (.not (elimFormula p)))
  | .ex p => elimExQF (elimFormula p)

def elimRecSpec : FormulaRecSpec Formula Formula where
  defaultF := .truth false
  fTruth := fun _ b => .truth b
  fEq := fun _ a b => .eq a b
  fLt := fun _ a b => .lt a b
  fLe := fun _ a b => .le a b
  fNot := fun _ p => .not p
  fAnd := fun _ p q => .and p q
  fOr := fun _ p q => .or p q
  fAll := fun _ p => .not (elimExQF (.not p))
  fEx := fun _ p => elimExQF p

theorem elimFormula_eq_rec (p : Formula) :
    elimFormula p = evalFormulaRec elimRecSpec p p := by
  have hgen : ∀ a : Formula, elimFormula p = evalFormulaRec elimRecSpec a p := by
    induction p with
    | truth b => intro _; rfl
    | eq t1 t2 => intro _; rfl
    | lt t1 t2 => intro _; rfl
    | le t1 t2 => intro _; rfl
    | not q ih => intro a; simp [elimFormula, evalFormulaRec, elimRecSpec, ih a]
    | and q r ihq ihr => intro a; simp [elimFormula, evalFormulaRec, elimRecSpec, ihq a, ihr a]
    | or q r ihq ihr => intro a; simp [elimFormula, evalFormulaRec, elimRecSpec, ihq a, ihr a]
    | all q ih => intro a; simp [elimFormula, evalFormulaRec, elimRecSpec, ih a]
    | ex q ih => intro a; simp [elimFormula, evalFormulaRec, elimRecSpec, ih a]
  exact hgen p

theorem computable_elimFormula : Computable elimFormula := by
  have hTruth : Computable (fun z : Formula × Bool => Formula.truth z.2) :=
    (primrec_formula_truth.comp Primrec.snd).to_comp
  have hEq : Computable (fun z : Formula × Term × Term => Formula.eq z.2.1 z.2.2) :=
    (primrec_formula_eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp
  have hLt : Computable (fun z : Formula × Term × Term => Formula.lt z.2.1 z.2.2) :=
    (primrec_formula_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp
  have hLe : Computable (fun z : Formula × Term × Term => Formula.le z.2.1 z.2.2) :=
    (primrec_formula_le.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp
  have hNot : Computable (fun z : Formula × Formula => Formula.not z.2) :=
    (primrec_formula_not.comp Primrec.snd).to_comp
  have hAnd : Computable (fun z : Formula × Formula × Formula => Formula.and z.2.1 z.2.2) :=
    (primrec_formula_and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp
  have hOr : Computable (fun z : Formula × Formula × Formula => Formula.or z.2.1 z.2.2) :=
    (primrec_formula_or.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp
  have hEx : Computable (fun z : Formula × Formula => elimExQF z.2) :=
    computable_elimExQF.comp Computable.snd
  have hAll : Computable (fun z : Formula × Formula => Formula.not (elimExQF (Formula.not z.2))) :=
    primrec_formula_not.to_comp.comp (computable_elimExQF.comp hNot)
  have hrec : Computable (fun p : Formula => evalFormulaRec elimRecSpec p p) :=
    computable_evalFormulaRec elimRecSpec Computable.id
      hTruth hEq hLt hLe hNot hAnd hOr hAll hEx
  exact hrec.of_eq (fun p => (elimFormula_eq_rec p).symm)

theorem isQF_elimFormula (p : Formula) : isQF (elimFormula p) = true := by
  induction p with
  | truth _ => rfl
  | eq _ _ => rfl
  | lt _ _ => rfl
  | le _ _ => rfl
  | not p ih => exact ih
  | and p q ihp ihq => simp [elimFormula, isQF, ihp, ihq]
  | or p q ihp ihq => simp [elimFormula, isQF, ihp, ihq]
  | all p _ => simp [elimFormula, isQF, isQF_elimExQF]
  | ex p _ => exact isQF_elimExQF _

theorem holds_elimFormula (p : Formula) (ρ : ℕ → ℝ) :
    (elimFormula p).Holds ρ ↔ p.Holds ρ := by
  induction p generalizing ρ with
  | truth _ => rfl
  | eq _ _ => rfl
  | lt _ _ => rfl
  | le _ _ => rfl
  | not p ih =>
    simp [elimFormula, Formula.Holds, ih ρ]
  | and p q ihp ihq =>
    simp [elimFormula, Formula.Holds, ihp ρ, ihq ρ]
  | or p q ihp ihq =>
    simp [elimFormula, Formula.Holds, ihp ρ, ihq ρ]
  | all p ih =>
    have hqf : isQF (.not (elimFormula p)) = true := isQF_elimFormula p
    simp only [elimFormula, Formula.Holds, holds_elimExQF hqf ρ, ih]
    rw [not_exists_not]
  | ex p ih =>
    have hqf : isQF (elimFormula p) = true := isQF_elimFormula p
    simp only [elimFormula, Formula.Holds, holds_elimExQF hqf ρ, ih]

abbrev NatPair := ℕ × ℕ

def npToReal (x : NatPair) : ℝ := (x.1 : ℝ) - (x.2 : ℝ)

def npAdd (x y : NatPair) : NatPair := (x.1 + y.1, x.2 + y.2)
def npNeg (x : NatPair) : NatPair := (x.2, x.1)
def npMul (x y : NatPair) : NatPair := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def npEq (x y : NatPair) : Bool := decide (x.1 + y.2 = y.1 + x.2)
def npLt (x y : NatPair) : Bool := decide (x.1 + y.2 < y.1 + x.2)
def npLe (x y : NatPair) : Bool := decide (x.1 + y.2 ≤ y.1 + x.2)

theorem primrec_npAdd : Primrec₂ npAdd :=
  ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

theorem primrec_npNeg : Primrec npNeg :=
  Primrec.snd.pair Primrec.fst

theorem primrec_npMul : Primrec₂ npMul := by
  have x1 : Primrec (fun z : NatPair × NatPair => z.1.1) := Primrec.fst.comp Primrec.fst
  have x2 : Primrec (fun z : NatPair × NatPair => z.1.2) := Primrec.snd.comp Primrec.fst
  have y1 : Primrec (fun z : NatPair × NatPair => z.2.1) := Primrec.fst.comp Primrec.snd
  have y2 : Primrec (fun z : NatPair × NatPair => z.2.2) := Primrec.snd.comp Primrec.snd
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp x1 y1) (Primrec.nat_mul.comp x2 y2)).pair
    (Primrec.nat_add.comp (Primrec.nat_mul.comp x1 y2) (Primrec.nat_mul.comp x2 y1))).to₂

theorem primrec_npEq : Primrec₂ npEq := by
  have lhs : Primrec (fun z : NatPair × NatPair => z.1.1 + z.2.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have rhs : Primrec (fun z : NatPair × NatPair => z.2.1 + z.1.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  exact ((Primrec.eq.comp lhs rhs).decide).to₂

theorem primrec_npLt : Primrec₂ npLt := by
  have lhs : Primrec (fun z : NatPair × NatPair => z.1.1 + z.2.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have rhs : Primrec (fun z : NatPair × NatPair => z.2.1 + z.1.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  exact ((Primrec.nat_lt.comp lhs rhs).decide).to₂

theorem primrec_npLe : Primrec₂ npLe := by
  have lhs : Primrec (fun z : NatPair × NatPair => z.1.1 + z.2.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have rhs : Primrec (fun z : NatPair × NatPair => z.2.1 + z.1.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
  exact ((Primrec.nat_le.comp lhs rhs).decide).to₂

theorem npToReal_npAdd (x y : NatPair) :
    npToReal (npAdd x y) = npToReal x + npToReal y := by
  simp only [npToReal, npAdd, Nat.cast_add]
  ring

theorem npToReal_npNeg (x : NatPair) :
    npToReal (npNeg x) = - npToReal x := by
  simp only [npToReal, npNeg]
  ring

theorem npToReal_npMul (x y : NatPair) :
    npToReal (npMul x y) = npToReal x * npToReal y := by
  simp only [npToReal, npMul, Nat.cast_add, Nat.cast_mul]
  ring

theorem npEq_eq_true_iff (x y : NatPair) :
    npEq x y = true ↔ npToReal x = npToReal y := by
  simp only [npEq, decide_eq_true_eq, npToReal]
  constructor
  · intro h
    have hR : ((x.1 + y.2 : ℕ) : ℝ) = ((y.1 + x.2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hR
    linarith
  · intro h
    have hR : ((x.1 + y.2 : ℕ) : ℝ) = ((y.1 + x.2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR

theorem npLt_eq_true_iff (x y : NatPair) :
    npLt x y = true ↔ npToReal x < npToReal y := by
  simp only [npLt, decide_eq_true_eq, npToReal]
  constructor
  · intro h
    have hR : ((x.1 + y.2 : ℕ) : ℝ) < ((y.1 + x.2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hR
    linarith
  · intro h
    have hR : ((x.1 + y.2 : ℕ) : ℝ) < ((y.1 + x.2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR

theorem npLe_eq_true_iff (x y : NatPair) :
    npLe x y = true ↔ npToReal x ≤ npToReal y := by
  simp only [npLe, decide_eq_true_eq, npToReal]
  constructor
  · intro h
    have hR : ((x.1 + y.2 : ℕ) : ℝ) ≤ ((y.1 + x.2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hR
    linarith
  · intro h
    have hR : ((x.1 + y.2 : ℕ) : ℝ) ≤ ((y.1 + x.2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR

def evalTermZero : Term → NatPair
  | .var _ => (0, 0)
  | .zero => (0, 0)
  | .one => (1, 0)
  | .add a b => npAdd (evalTermZero a) (evalTermZero b)
  | .mul a b => npMul (evalTermZero a) (evalTermZero b)
  | .neg a => npNeg (evalTermZero a)

theorem npToReal_evalTermZero (t : Term) :
    npToReal (evalTermZero t) = t.eval (fun _ => 0) := by
  induction t with
  | var _ => simp [evalTermZero, npToReal, Term.eval]
  | zero => simp [evalTermZero, npToReal, Term.eval]
  | one => simp [evalTermZero, npToReal, Term.eval]
  | add a b iha ihb =>
    simp [evalTermZero, npToReal_npAdd, iha, ihb, Term.eval]
  | mul a b iha ihb =>
    simp [evalTermZero, npToReal_npMul, iha, ihb, Term.eval]
  | neg a iha =>
    simp [evalTermZero, npToReal_npNeg, iha, Term.eval]

def stepTermZero (s : List NatPair) (tok : Token) : List NatPair :=
  let e0 := s.getD 0 (0, 0)
  let e1 := s.getD 1 (0, 0)
  if tok.1 = 0 then (0, 0) :: s
  else if tok.1 = 1 then (0, 0) :: s
  else if tok.1 = 2 then (1, 0) :: s
  else if tok.1 = 3 then npAdd e1 e0 :: s.drop 2
  else if tok.1 = 4 then npMul e1 e0 :: s.drop 2
  else if tok.1 = 5 then npNeg e0 :: s.drop 1
  else s

def runTermZero (c : Code) (s : List NatPair) : List NatPair :=
  c.foldl stepTermZero s

theorem runTermZero_append (c1 c2 : Code) (s : List NatPair) :
    runTermZero (c1 ++ c2) s = runTermZero c2 (runTermZero c1 s) :=
  List.foldl_append

theorem runTermZero_term_code (t : Term) (s : List NatPair) :
    runTermZero t.code s = evalTermZero t :: s := by
  induction t generalizing s with
  | var _ => rfl
  | zero => rfl
  | one => rfl
  | add a b iha ihb =>
    simp only [Term.code, runTermZero_append, iha, ihb]
    rfl
  | mul a b iha ihb =>
    simp only [Term.code, runTermZero_append, iha, ihb]
    rfl
  | neg a iha =>
    simp only [Term.code, runTermZero_append, iha]
    rfl

theorem evalTermZero_eq_run (t : Term) :
    evalTermZero t = (runTermZero t.code []).getD 0 (0, 0) := by
  rw [runTermZero_term_code]
  rfl

theorem primrec_stepTermZero : Primrec₂ stepTermZero := by
  let Z := List NatPair × Token
  have hs : Primrec (fun z : Z => z.1) := Primrec.fst
  have htag : Primrec (fun z : Z => z.2.1) := Primrec.fst.comp Primrec.snd
  have he0 : Primrec (fun z : Z => z.1.getD 0 (0, 0)) :=
    (Primrec.list_getD ((0, 0) : NatPair)).comp hs (Primrec.const 0)
  have he1 : Primrec (fun z : Z => z.1.getD 1 (0, 0)) :=
    (Primrec.list_getD ((0, 0) : NatPair)).comp hs (Primrec.const 1)
  have hdrop1 : Primrec (fun z : Z => z.1.drop 1) :=
    Primrec.list_drop.comp (Primrec.const 1) hs
  have hdrop2 : Primrec (fun z : Z => z.1.drop 2) :=
    Primrec.list_drop.comp (Primrec.const 2) hs
  have hb01 : Primrec (fun z : Z => ((0, 0) : NatPair) :: z.1) :=
    Primrec.list_cons.comp (Primrec.const ((0, 0) : NatPair)) hs
  have hb2 : Primrec (fun z : Z => ((1, 0) : NatPair) :: z.1) :=
    Primrec.list_cons.comp (Primrec.const ((1, 0) : NatPair)) hs
  have hb3 : Primrec (fun z : Z => npAdd (z.1.getD 1 (0, 0)) (z.1.getD 0 (0, 0)) :: z.1.drop 2) :=
    Primrec.list_cons.comp (primrec_npAdd.comp he1 he0) hdrop2
  have hb4 : Primrec (fun z : Z => npMul (z.1.getD 1 (0, 0)) (z.1.getD 0 (0, 0)) :: z.1.drop 2) :=
    Primrec.list_cons.comp (primrec_npMul.comp he1 he0) hdrop2
  have hb5 : Primrec (fun z : Z => npNeg (z.1.getD 0 (0, 0)) :: z.1.drop 1) :=
    Primrec.list_cons.comp (primrec_npNeg.comp he0) hdrop1
  exact (Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hb01
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hb01
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hb2
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) hb3
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) hb4
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) hb5 hs)))))).to₂

theorem primrec_evalTermZero : Primrec evalTermZero := by
  have hfold : Primrec (fun t : Term => runTermZero t.code []) :=
    Primrec.list_foldl primrec_term_code (Primrec.const ([] : List NatPair))
      (primrec_stepTermZero.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  have hout : Primrec (fun t : Term => (runTermZero t.code []).getD 0 (0, 0)) :=
    (Primrec.list_getD ((0, 0) : NatPair)).comp hfold (Primrec.const 0)
  exact hout.of_eq (fun t => (evalTermZero_eq_run t).symm)

def evalFormulaZero : Formula → Bool
  | .truth b => b
  | .eq a b => npEq (evalTermZero a) (evalTermZero b)
  | .lt a b => npLt (evalTermZero a) (evalTermZero b)
  | .le a b => npLe (evalTermZero a) (evalTermZero b)
  | .not p => !(evalFormulaZero p)
  | .and p q => evalFormulaZero p && evalFormulaZero q
  | .or p q => evalFormulaZero p || evalFormulaZero q
  | .all _ => false
  | .ex _ => false

def evalZeroRecSpec : FormulaRecSpec Unit Bool where
  defaultF := false
  fTruth := fun _ b => b
  fEq := fun _ a b => npEq (evalTermZero a) (evalTermZero b)
  fLt := fun _ a b => npLt (evalTermZero a) (evalTermZero b)
  fLe := fun _ a b => npLe (evalTermZero a) (evalTermZero b)
  fNot := fun _ b => !b
  fAnd := fun _ b1 b2 => b1 && b2
  fOr := fun _ b1 b2 => b1 || b2
  fAll := fun _ _ => false
  fEx := fun _ _ => false

theorem evalFormulaZero_eq_rec (p : Formula) :
    evalFormulaZero p = evalFormulaRec evalZeroRecSpec () p := by
  induction p <;> simp_all [evalFormulaZero, evalFormulaRec, evalZeroRecSpec]

theorem primrec_evalFormulaZero : Primrec evalFormulaZero := by
  have hA : Primrec (fun z : Unit × Term × Term => evalTermZero z.2.1) :=
    primrec_evalTermZero.comp (Primrec.fst.comp Primrec.snd)
  have hB : Primrec (fun z : Unit × Term × Term => evalTermZero z.2.2) :=
    primrec_evalTermZero.comp (Primrec.snd.comp Primrec.snd)
  have hEq : Primrec (fun z : Unit × Term × Term => npEq (evalTermZero z.2.1) (evalTermZero z.2.2)) :=
    primrec_npEq.comp hA hB
  have hLt : Primrec (fun z : Unit × Term × Term => npLt (evalTermZero z.2.1) (evalTermZero z.2.2)) :=
    primrec_npLt.comp hA hB
  have hLe : Primrec (fun z : Unit × Term × Term => npLe (evalTermZero z.2.1) (evalTermZero z.2.2)) :=
    primrec_npLe.comp hA hB
  have hNot : Primrec (fun z : Unit × Bool => !z.2) :=
    Primrec.not.comp Primrec.snd
  have hAnd : Primrec (fun z : Unit × Bool × Bool => z.2.1 && z.2.2) :=
    Primrec.and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hOr : Primrec (fun z : Unit × Bool × Bool => z.2.1 || z.2.2) :=
    Primrec.or.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hrec : Primrec (fun p : Formula => evalFormulaRec evalZeroRecSpec () p) :=
    primrec_evalFormulaRec (spec := evalZeroRecSpec) (Primrec.const ()) Primrec.id
      Primrec.snd hEq hLt hLe hNot hAnd hOr (Primrec.const false) (Primrec.const false)
  exact hrec.of_eq (fun p => (evalFormulaZero_eq_rec p).symm)

theorem evalFormulaZero_eq_true_iff_of_isQF {p : Formula} (hp : isQF p = true) :
    evalFormulaZero p = true ↔ p.Holds (fun _ => 0) := by
  induction p with
  | truth b =>
    simp [evalFormulaZero, Formula.Holds]
  | eq a b =>
    simp [evalFormulaZero, npEq_eq_true_iff, npToReal_evalTermZero, Formula.Holds]
  | lt a b =>
    simp [evalFormulaZero, npLt_eq_true_iff, npToReal_evalTermZero, Formula.Holds]
  | le a b =>
    simp [evalFormulaZero, npLe_eq_true_iff, npToReal_evalTermZero, Formula.Holds]
  | not p ih =>
    simp only [isQF] at hp
    rw [evalFormulaZero, Bool.not_eq_true', ← Bool.not_eq_true, ih hp]
    rfl
  | and p q ihp ihq =>
    simp only [isQF, Bool.and_eq_true] at hp
    simp [evalFormulaZero, Formula.Holds, ihp hp.1, ihq hp.2]
  | or p q ihp ihq =>
    simp only [isQF, Bool.and_eq_true] at hp
    simp [evalFormulaZero, Formula.Holds, ihp hp.1, ihq hp.2]
  | all _ => cases hp
  | ex _ => cases hp

def decideFormulaZero (p : Formula) : Bool :=
  evalFormulaZero (elimFormula p)

theorem computable_decideFormulaZero : Computable decideFormulaZero :=
  primrec_evalFormulaZero.to_comp.comp computable_elimFormula

theorem decideFormulaZero_eq_true_iff (p : Formula) :
    decideFormulaZero p = true ↔ p.Holds (fun _ => 0) := by
  rw [decideFormulaZero, evalFormulaZero_eq_true_iff_of_isQF (isQF_elimFormula p),
    holds_elimFormula]

def decideCodeZero (c : Code) : Bool :=
  ((decode c).map decideFormulaZero).getD false

theorem computable_decideCodeZero : Computable decideCodeZero := by
  have hmap : Computable (fun c : Code => (decode c).map decideFormulaZero) :=
    Computable.option_map primrec_decode.to_comp (computable_decideFormulaZero.comp Computable.snd).to₂
  exact Primrec.option_getD.to_comp.comp hmap (Computable.const false)

theorem decideCodeZero_code (p : Formula) :
    decideCodeZero p.code = decideFormulaZero p := by
  simp [decideCodeZero, decode_code]

theorem decideCodeZero_eq_true_iff_of_code (p : Formula) :
    decideCodeZero p.code = true ↔ CodeHolds p.code (fun _ => 0) := by
  rw [decideCodeZero_code, codeHolds_code, decideFormulaZero_eq_true_iff]

end Grunbaum2003.FormulaCompiler.Parametric

namespace Grunbaum2003

lemma extremePoints_eq_exposedSingletons_m05_sr {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
  classical
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_in_P : x ∈ P := extremePoints_subset hx
    have hx_ext : IsExtreme ℝ P {x} := isExtreme_singleton.mpr hx
    have hx_not_in : x ∉ convexHull ℝ (V0 \ {x}) := by
      intro hx_in
      have h_sub : convexHull ℝ (V0 \ {x}) ⊆ P := by
        rw [hP_eq]
        exact convexHull_mono Set.diff_subset
      have hx_ext' : IsExtreme ℝ (convexHull ℝ (V0 \ {x})) {x} :=
        hx_ext.mono h_sub (Set.singleton_subset_iff.mpr hx_in)
      have hx_ep : x ∈ (convexHull ℝ (V0 \ {x})).extremePoints ℝ :=
        isExtreme_singleton.mp hx_ext'
      have hx_diff : x ∈ V0 \ {x} := extremePoints_convexHull_subset hx_ep
      exact hx_diff.2 rfl
    have hC_conv : Convex ℝ (convexHull ℝ (V0 \ {x})) := convex_convexHull ℝ _
    have hC_closed : IsClosed (convexHull ℝ (V0 \ {x})) :=
      ((hV0_fin.diff).isCompact_convexHull ℝ).isClosed
    obtain ⟨l, u, hlu, hux⟩ := geometric_hahn_banach_closed_point hC_conv hC_closed hx_not_in
    intro _
    refine ⟨l, ?_⟩
    apply Set.Subset.antisymm
    · rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      refine ⟨hx_in_P, ?_⟩
      have h_le : P ⊆ {z : Fin d → ℝ | l z ≤ l x} := by
        rw [hP_eq]
        refine convexHull_min ?_ ?_
        · intro s hs
          change l s ≤ l x
          by_cases hsx : s = x
          · rw [hsx]
          · have hs_diff : s ∈ V0 \ {x} := ⟨hs, hsx⟩
            exact le_of_lt ((hlu s (subset_convexHull ℝ _ hs_diff)).trans hux)
        · intro z1 hz1 z2 hz2 a b ha hb hab
          change l z1 ≤ l x at hz1
          change l z2 ≤ l x at hz2
          change l (a • z1 + b • z2) ≤ l x
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have hb_eq : b = 1 - a := by linarith
          subst hb_eq
          nlinarith
      intro z hz
      exact h_le hz
    · rintro y ⟨hyP, hymax⟩
      rw [Set.mem_singleton_iff]
      have hly : l x ≤ l y := hymax x hx_in_P
      rw [hP_eq] at hyP
      let Vfin := hV0_fin.toFinset
      have hVfin : (Vfin : Set (Fin d → ℝ)) = V0 := hV0_fin.coe_toFinset
      rw [← hVfin] at hyP
      obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.mp hyP
      have h_sum_nonneg : ∀ s ∈ Vfin, 0 ≤ w s * (l x - l s) := by
        intro s hs
        refine mul_nonneg (hw0 s hs) ?_
        by_cases hsx : s = x
        · subst hsx; linarith
        · have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
          have hls := hlu s (subset_convexHull ℝ _ hs_diff)
          linarith
      have h_sum_le : ∑ s ∈ Vfin, w s * (l x - l s) ≤ 0 := by
        have h_eq : ∑ s ∈ Vfin, w s * (l x - l s) = l x - l (∑ s ∈ Vfin, w s • s) := by
          rw [map_sum]
          simp_rw [map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
            hw1, one_mul]
        linarith
      have h_all_zero : ∀ s ∈ Vfin, w s * (l x - l s) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg h_sum_nonneg).mp
          (le_antisymm h_sum_le (Finset.sum_nonneg h_sum_nonneg))
      have hw_zero_of_ne : ∀ s ∈ Vfin, s ≠ x → w s = 0 := by
        intro s hs hsx
        have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
        have hls := (hlu s (subset_convexHull ℝ _ hs_diff)).trans hux
        have h_z := h_all_zero s hs
        rcases mul_eq_zero.mp h_z with hw_z | hl_z
        · exact hw_z
        · linarith
      calc ∑ s ∈ Vfin, w s • s
          = ∑ s ∈ Vfin, w s • x := by
            refine Finset.sum_congr rfl (fun s hs => ?_)
            by_cases hsx : s = x
            · subst hsx; rfl
            · simp [hw_zero_of_ne s hs hsx]
        _ = (∑ s ∈ Vfin, w s) • x := (Finset.sum_smul).symm
        _ = x := by rw [hw1, one_smul]
  · intro x hx
    exact exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hx)

theorem polytope_face_eq_convexHull_exposed_vertices_sr (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ F : PolytopeFace P,
        F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := by
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hExtEq : P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
    extremePoints_eq_exposedSingletons_m05_sr P hP
  have hVertFin : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite := by
    rw [← hExtEq, hP_eq]
    exact hV0_fin.subset extremePoints_convexHull_subset
  refine ⟨hVertFin, ?_⟩
  intro F
  have hP_comp : IsCompact P := hP_eq ▸ hV0_fin.isCompact_convexHull ℝ
  have hP_conv : Convex ℝ P := hP_eq ▸ convex_convexHull ℝ V0
  have hF_comp : IsCompact F.val := F.property.isCompact hP_comp
  have hF_conv : Convex ℝ F.val := F.property.convex hP_conv
  have hF_ext : F.val.extremePoints ℝ = F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
    rw [F.property.isExtreme.extremePoints_eq, ← hExtEq]
  have h_km := closure_convexHull_extremePoints hF_comp hF_conv
  rw [hF_ext] at h_km
  have h_closed : IsClosed (convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) :=
    ((hVertFin.subset Set.inter_subset_right).isCompact_convexHull ℝ).isClosed
  rw [h_closed.closure_eq] at h_km
  exact h_km.symm

end Grunbaum2003

namespace Grunbaum2003

theorem computable_list_foldl_sr {A B C : Type*} [Primcodable A] [Primcodable B]
    [Primcodable C] {f : A → List B} {g : A → C} {h : A → C × B → C}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun c b => h a (c, b)) (g a)) := by
  let G (a : A) (s : List B × C) : List B × C :=
    List.casesOn s.1 s (fun b l => (l, h a (s.2, b)))
  have hG : Computable₂ G := by
    have hHead : Computable (fun t : A × (List B × C) => t.2.1.head?) :=
      Primrec.list_head?.to_comp.comp (Computable.fst.comp Computable.snd)
    have hTail : Computable (fun u : (A × (List B × C)) × B => u.1.2.1.tail) :=
      Primrec.list_tail.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    have hNew : Computable (fun u : (A × (List B × C)) × B => h u.1.1 (u.1.2.2, u.2)) :=
      hh.comp (Computable.fst.comp Computable.fst)
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
    have hCase := Computable.option_casesOn hHead Computable.snd (hTail.pair hNew).to₂
    exact (hCase.of_eq (g := fun t : A × (List B × C) => G t.1 t.2) (fun ⟨a, l, c⟩ => by cases l <;> rfl)).to₂
  have hI : Computable (fun a => Nat.rec (motive := fun _ => List B × C) (f a, g a)
      (fun _ s => G a s) (f a).length) :=
    Computable.nat_rec (Computable.list_length.comp hf) (hf.pair hg)
      (hG.comp Computable.fst (Computable.snd.comp Computable.snd)).to₂
  have hRec (a : A) (l : List B) (c : C) (n : ℕ) :
      Nat.rec (motive := fun _ => List B × C) (l, c) (fun _ s => G a s) n = (G a)^[n] (l, c) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        change G a (Nat.rec (motive := fun _ => List B × C) (l, c) (fun _ s => G a s) n) = _
        rw [ih, Function.iterate_succ_apply']
  have hEval (a : A) (l : List B) (c : C) (n : ℕ) :
      (G a)^[n] (l, c) =
        (l.drop n, (l.take n).foldl (fun c b => h a (c, b)) c) := by
    induction n generalizing l c with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply]
        cases l <;> simp only [G, ih,
          List.drop_nil, List.take_nil, List.foldl_nil, List.drop_succ_cons,
          List.take_succ_cons, List.foldl_cons]
  apply (Computable.snd.comp hI).of_eq
  intro a
  rw [hRec, hEval]
  simp only [List.take_length]

theorem computable_list_foldr {A B C : Type*} [Primcodable A] [Primcodable B]
    [Primcodable C] {f : A → List B} {g : A → C} {h : A → B × C → C}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldr (fun b c => h a (b, c)) (g a)) := by
  have h := computable_list_foldl_sr (Computable.list_reverse.comp hf) hg
    ((hh.comp Computable.fst ((Computable.snd.pair Computable.fst).comp Computable.snd)).to₂)
  exact h.of_eq (fun a => by simp only [List.foldl_reverse])

theorem computable_list_filter {A B : Type*} [Primcodable A] [Primcodable B]
    {f : A → List B} {p : A → B → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a => (f a).filter (p a)) := by
  have hStep : Computable (fun t : A × (B × List B) =>
      cond (p t.1 t.2.1) (t.2.1 :: t.2.2) t.2.2) :=
    Computable.cond (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.list_cons.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)) (Computable.snd.comp Computable.snd)
  have h := computable_list_foldr hf (Computable.const []) hStep.to₂
  apply h.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih =>
      simp only [List.foldr_cons, List.filter_cons, ih]
      cases p a b <;> rfl

end Grunbaum2003

namespace Grunbaum2003

theorem primrec_list_pwFilter {A : Type*} [Primcodable A] {R : A → A → Prop}
    [DecidableRel R] (hR : PrimrecRel R) : Primrec (fun L : List A => L.pwFilter R) := by
  unfold List.pwFilter
  apply Primrec.list_foldr
    (h := fun (_ : List A) (p : A × List A) =>
      if ∀ b ∈ p.2, R p.1 b then p.1 :: p.2 else p.2)
    Primrec.id (Primrec.const [])
  change Primrec (fun t : List A × (A × List A) =>
    if ∀ b ∈ t.2.2, R t.2.1 b then t.2.1 :: t.2.2 else t.2.2)
  exact Primrec.ite
    (hR.swap.forall_mem_list.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

theorem pwFilter_complement_covers {A : Type*} {R : A → A → Prop}
    [DecidableRel R] (hR : Equivalence R) (L : List A) :
    (L.pwFilter (fun a b => ¬ R a b)) ⊆ L ∧
      ∀ a ∈ L, ∃ b ∈ L.pwFilter (fun a b => ¬ R a b), R a b := by
  classical
  refine ⟨List.pwFilter_subset L, ?_⟩
  intro a ha
  by_contra h
  have hAll : ∀ b ∈ L.pwFilter (fun a b => ¬ R a b), ¬ R a b := by
    intro b hb hab
    exact h ⟨b, hb, hab⟩
  have hNegTrans : ∀ {x y z : A}, (¬ R x z) → (¬ R x y) ∨ (¬ R y z) := by
    intro x y z hxz
    by_cases hxy : R x y
    · exact Or.inr (fun hyz => hxz (hR.trans hxy hyz))
    · exact Or.inl hxy
  have hOrig := (List.forall_mem_pwFilter (R := fun x y : A => ¬ R x y) hNegTrans a L).mp hAll
  exact hOrig a ha (hR.refl a)

theorem pwFilter_complement_unique_indices {A : Type*} {R : A → A → Prop}
    [DecidableRel R] (hR : Equivalence R) (L : List A)
    (i j : Fin (L.pwFilter (fun a b => ¬ R a b)).length)
    (hij : R ((L.pwFilter (fun a b => ¬ R a b)).get i)
      ((L.pwFilter (fun a b => ¬ R a b)).get j)) : i = j := by
  have hPair := List.pairwise_pwFilter (R := fun a b => ¬ R a b) L
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hPair.rel_get_of_lt hlt) hij
  · exact (hPair.rel_get_of_lt hgt) (hR.symm hij)

end Grunbaum2003

namespace Grunbaum2003

theorem primrec_parameterized_pwFilter {K A : Type*} [Primcodable K] [Primcodable A]
    {R : K → A → A → Prop} [∀ k, DecidableRel (R k)]
    (hR : PrimrecRel (fun p : K × A => fun b => R p.1 p.2 b)) :
    Primrec₂ (fun k (L : List A) => L.pwFilter (R k)) := by
  unfold List.pwFilter
  apply Primrec.list_foldr
    (h := fun (p : K × List A) (s : A × List A) =>
      if ∀ b ∈ s.2, R p.1 s.1 b then s.1 :: s.2 else s.2)
    Primrec.snd (Primrec.const [])
  change Primrec (fun t : (K × List A) × (A × List A) =>
    if ∀ b ∈ t.2.2, R t.1.1 t.2.1 b then t.2.1 :: t.2.2 else t.2.2)
  exact Primrec.ite
    (hR.swap.forall_mem_list.comp (Primrec.snd.comp Primrec.snd)
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

end Grunbaum2003

namespace Grunbaum2003

private def relationEntry (A : List (List Bool)) (i j : ℕ) : Bool :=
  (A.getD i []).getD j false

private theorem relationEntry_eq_get (A : List (List Bool))
    (i j : Fin A.length) :
    relationEntry A i.val j.val = ((A.get i)[j.val]?).getD false := by
  unfold relationEntry
  rw [List.getD_eq_get A [] i, List.getD_eq_getElem?_getD]

private def relationCertificate (A B : List (List Bool)) (R : List (ℕ × ℕ)) : Prop :=
  (∀ i ∈ List.range A.length, ∃ j ∈ List.range B.length, (i, j) ∈ R) ∧
  (∀ j ∈ List.range B.length, ∃ i ∈ List.range A.length, (i, j) ∈ R) ∧
  ∀ p ∈ R, ∀ q ∈ R,
    (p.1 = q.1 ↔ p.2 = q.2) ∧
      relationEntry A p.1 q.1 = relationEntry B p.2 q.2

private instance relationCertificate_decidable (A B : List (List Bool)) (R : List (ℕ × ℕ)) :
    Decidable (relationCertificate A B R) := by
  unfold relationCertificate
  infer_instance

def finiteRelationIsoCheck (A B : List (List Bool)) : Bool :=
  decide (∃ R ∈ ((List.range A.length).product (List.range B.length)).sublists',
    relationCertificate A B R)

theorem finiteRelationIsoCheck_eq_true_iff (A B : List (List Bool)) :
    finiteRelationIsoCheck A B = true ↔
      ∃ e : Fin A.length ≃ Fin B.length, ∀ i j,
        ((A.get i)[j.val]?).getD false =
          ((B.get (e i))[(e j).val]?).getD false := by
  classical
  unfold finiteRelationIsoCheck
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨R, _, hTotalA, hTotalB, hGraph⟩
    have hExists (i : Fin A.length) : ∃ j : Fin B.length, (i.val, j.val) ∈ R := by
      obtain ⟨j, hj, hij⟩ := hTotalA i.val (List.mem_range.mpr i.isLt)
      exact ⟨⟨j, List.mem_range.mp hj⟩, hij⟩
    choose f hf using hExists
    have hfInj : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      exact ((hGraph (i.val, (f i).val) (hf i) (j.val, (f j).val) (hf j)).1).mpr
        (congrArg Fin.val hij)
    have hfSurj : Function.Surjective f := by
      intro j
      obtain ⟨i, hi, hij⟩ := hTotalB j.val (List.mem_range.mpr j.isLt)
      let i' : Fin A.length := ⟨i, List.mem_range.mp hi⟩
      refine ⟨i', Fin.ext ?_⟩
      exact ((hGraph (i, (f i').val) (hf i') (i, j.val) hij).1).mp rfl
    refine ⟨Equiv.ofBijective f ⟨hfInj, hfSurj⟩, ?_⟩
    intro i j
    change ((A.get i)[j.val]?).getD false = ((B.get (f i))[(f j).val]?).getD false
    have h := (hGraph (i.val, (f i).val) (hf i) (j.val, (f j).val) (hf j)).2
    rw [relationEntry_eq_get A i j, relationEntry_eq_get B (f i) (f j)] at h
    exact h
  · rintro ⟨e, he⟩
    let f : ℕ → ℕ := fun i => if hi : i < A.length then (e ⟨i, hi⟩).val else 0
    let base := (List.range A.length).product (List.range B.length)
    let R := base.filter (fun p => p.2 == f p.1)
    have hMem (p : ℕ × ℕ) : p ∈ R ↔
        p.1 < A.length ∧ p.2 < B.length ∧ p.2 = f p.1 := by
      rcases p with ⟨i, j⟩
      have hProduct : (i, j) ∈ base ↔ i < A.length ∧ j < B.length :=
        List.mem_product.trans (and_congr List.mem_range List.mem_range)
      simp only [R, List.mem_filter, hProduct, beq_iff_eq, and_assoc]
    refine ⟨R, List.mem_sublists'.mpr List.filter_sublist, ?_, ?_, ?_⟩
    · intro i hi
      have hi' : i < A.length := List.mem_range.mp hi
      let i' : Fin A.length := ⟨i, hi'⟩
      refine ⟨(e i').val, List.mem_range.mpr (e i').isLt,
        (hMem _).mpr ⟨hi', (e i').isLt, ?_⟩⟩
      simp only [f, dif_pos hi']
      rfl
    · intro j hj
      have hj' : j < B.length := List.mem_range.mp hj
      let j' : Fin B.length := ⟨j, hj'⟩
      let i' := e.symm j'
      refine ⟨i'.val, List.mem_range.mpr i'.isLt,
        (hMem _).mpr ⟨i'.isLt, hj', ?_⟩⟩
      have hfi : f i'.val = (e i').val := by simp only [f, dif_pos i'.isLt]
      rw [hfi]
      exact (congrArg Fin.val (e.apply_symm_apply j')).symm
    · intro p hp q hq
      obtain ⟨hpA, _, hpf⟩ := (hMem p).mp hp
      obtain ⟨hqA, _, hqf⟩ := (hMem q).mp hq
      let ip : Fin A.length := ⟨p.1, hpA⟩
      let iq : Fin A.length := ⟨q.1, hqA⟩
      have hp₂ : p.2 = (e ip).val := by
        rw [hpf]
        simp only [f, dif_pos hpA]
        rfl
      have hq₂ : q.2 = (e iq).val := by
        rw [hqf]
        simp only [f, dif_pos hqA]
        rfl
      constructor
      · constructor
        · intro hpq
          have hi : ip = iq := Fin.ext hpq
          exact hp₂.trans ((congrArg (fun i : Fin A.length => (e i).val) hi).trans hq₂.symm)
        · intro hpq
          have heq : e ip = e iq := Fin.ext (hp₂.symm.trans (hpq.trans hq₂))
          exact congrArg Fin.val (e.injective heq)
      · have h := he ip iq
        rw [← relationEntry_eq_get A ip iq,
          ← relationEntry_eq_get B (e ip) (e iq)] at h
        rw [hp₂, hq₂]
        exact h

private theorem primrec_relationEntry_comp {α : Type} [Primcodable α]
    {A : α → List (List Bool)} {i j : α → ℕ}
    (hA : Primrec A) (hi : Primrec i) (hj : Primrec j) :
    Primrec (fun x => relationEntry (A x) (i x) (j x)) := by
  unfold relationEntry
  exact (Primrec.list_getD false).comp ((Primrec.list_getD []).comp hA hi) hj

private abbrev IsoData := (List (List Bool) × List (List Bool)) × List (ℕ × ℕ)

private theorem primrec_relationTotalA : PrimrecPred (fun x : IsoData =>
    ∀ i ∈ List.range x.1.1.length, ∃ j ∈ List.range x.1.2.length, (i, j) ∈ x.2) := by
    apply primrec_bounded_list_forall
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))
    change PrimrecPred (fun y : IsoData × ℕ =>
      ∃ j ∈ List.range y.1.1.2.length, (y.2, j) ∈ y.1.2)
    apply primrec_bounded_list_exists
      (Primrec.list_range.comp (Primrec.list_length.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
    change PrimrecPred (fun z : (IsoData × ℕ) × ℕ => (z.1.2, z.2) ∈ z.1.1.2)
    exact primrec_list_mem.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))

private theorem primrec_relationTotalB : PrimrecPred (fun x : IsoData =>
    ∀ j ∈ List.range x.1.2.length, ∃ i ∈ List.range x.1.1.length, (i, j) ∈ x.2) := by
    apply primrec_bounded_list_forall
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))
    change PrimrecPred (fun y : IsoData × ℕ =>
      ∃ i ∈ List.range y.1.1.1.length, (i, y.2) ∈ y.1.2)
    apply primrec_bounded_list_exists
      (Primrec.list_range.comp (Primrec.list_length.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    change PrimrecPred (fun z : (IsoData × ℕ) × ℕ => (z.2, z.1.2) ∈ z.1.1.2)
    exact primrec_list_mem.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))

private abbrev IsoGraphData := (IsoData × (ℕ × ℕ)) × (ℕ × ℕ)

private theorem primrec_relationGraphIff : PrimrecPred (fun z : IsoGraphData =>
    z.1.2.1 = z.2.1 ↔ z.1.2.2 = z.2.2) := by
  have hp₁ : Primrec (fun z : IsoGraphData => z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hp₂ : Primrec (fun z : IsoGraphData => z.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hq₁ : Primrec (fun z : IsoGraphData => z.2.1) := Primrec.fst.comp Primrec.snd
  have hq₂ : Primrec (fun z : IsoGraphData => z.2.2) := Primrec.snd.comp Primrec.snd
  apply (Primrec.eq.comp ((Primrec.eq.comp hp₁ hq₁).decide)
    ((Primrec.eq.comp hp₂ hq₂).decide)).of_eq
  intro z
  exact decide_eq_decide

private theorem primrec_relationGraphEntry : PrimrecPred (fun z : IsoGraphData =>
    relationEntry z.1.1.1.1 z.1.2.1 z.2.1 = relationEntry z.1.1.1.2 z.1.2.2 z.2.2) := by
  have hp₁ : Primrec (fun z : IsoGraphData => z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hp₂ : Primrec (fun z : IsoGraphData => z.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hq₁ : Primrec (fun z : IsoGraphData => z.2.1) := Primrec.fst.comp Primrec.snd
  have hq₂ : Primrec (fun z : IsoGraphData => z.2.2) := Primrec.snd.comp Primrec.snd
  have hA : Primrec (fun z : IsoGraphData => z.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hB : Primrec (fun z : IsoGraphData => z.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec.eq.comp
    (primrec_relationEntry_comp hA hp₁ hq₁)
    (primrec_relationEntry_comp hB hp₂ hq₂)

private theorem primrec_relationGraph : PrimrecPred (fun x : IsoData =>
    ∀ p ∈ x.2, ∀ q ∈ x.2,
      (p.1 = q.1 ↔ p.2 = q.2) ∧
        relationEntry x.1.1 p.1 q.1 = relationEntry x.1.2 p.2 q.2) := by
  apply primrec_bounded_list_forall Primrec.snd
  change PrimrecPred (fun y : IsoData × (ℕ × ℕ) => ∀ q ∈ y.1.2,
    (y.2.1 = q.1 ↔ y.2.2 = q.2) ∧
      relationEntry y.1.1.1 y.2.1 q.1 = relationEntry y.1.1.2 y.2.2 q.2)
  apply primrec_bounded_list_forall (Primrec.snd.comp Primrec.fst)
  exact primrec_relationGraphIff.and primrec_relationGraphEntry

private theorem primrec_relationCertificate :
    PrimrecPred (fun x : IsoData => relationCertificate x.1.1 x.1.2 x.2) :=
  primrec_relationTotalA.and (primrec_relationTotalB.and primrec_relationGraph)

theorem primrec_finiteRelationIsoCheck : Primrec₂ finiteRelationIsoCheck := by
  have hCandidates : Primrec (fun x : List (List Bool) × List (List Bool) =>
      ((List.range x.1.length).product (List.range x.2.length)).sublists') :=
    primrec_list_sublists.comp (primrec_list_product.comp
      (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
      (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)))
  have h : PrimrecPred (fun x : List (List Bool) × List (List Bool) =>
      ∃ R ∈ ((List.range x.1.length).product (List.range x.2.length)).sublists',
        relationCertificate x.1 x.2 R) :=
    primrec_bounded_list_exists hCandidates primrec_relationCertificate
  exact h.decide

end Grunbaum2003

open scoped BigOperators

namespace Grunbaum2003

lemma extremePoints_eq_exposedSingletons_sr {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
  classical
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_in_P : x ∈ P := extremePoints_subset hx
    have hx_ext : IsExtreme ℝ P {x} := isExtreme_singleton.mpr hx
    have hx_not_in : x ∉ convexHull ℝ (V0 \ {x}) := by
      intro hx_in
      have h_sub : convexHull ℝ (V0 \ {x}) ⊆ P := by
        rw [hP_eq]
        exact convexHull_mono Set.diff_subset
      have hx_ext' : IsExtreme ℝ (convexHull ℝ (V0 \ {x})) {x} :=
        hx_ext.mono h_sub (Set.singleton_subset_iff.mpr hx_in)
      have hx_ep : x ∈ (convexHull ℝ (V0 \ {x})).extremePoints ℝ :=
        isExtreme_singleton.mp hx_ext'
      have hx_diff : x ∈ V0 \ {x} := extremePoints_convexHull_subset hx_ep
      exact hx_diff.2 rfl
    have hC_conv : Convex ℝ (convexHull ℝ (V0 \ {x})) := convex_convexHull ℝ _
    have hC_closed : IsClosed (convexHull ℝ (V0 \ {x})) :=
      ((hV0_fin.diff).isCompact_convexHull ℝ).isClosed
    obtain ⟨l, u, hlu, hux⟩ := geometric_hahn_banach_closed_point hC_conv hC_closed hx_not_in
    intro _
    refine ⟨l, ?_⟩
    apply Set.Subset.antisymm
    · rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      refine ⟨hx_in_P, ?_⟩
      have h_le : P ⊆ {z : Fin d → ℝ | l z ≤ l x} := by
        rw [hP_eq]
        refine convexHull_min ?_ ?_
        · intro s hs
          change l s ≤ l x
          by_cases hsx : s = x
          · rw [hsx]
          · have hs_diff : s ∈ V0 \ {x} := ⟨hs, hsx⟩
            exact le_of_lt ((hlu s (subset_convexHull ℝ _ hs_diff)).trans hux)
        · intro z1 hz1 z2 hz2 a b ha hb hab
          change l z1 ≤ l x at hz1
          change l z2 ≤ l x at hz2
          change l (a • z1 + b • z2) ≤ l x
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have hb_eq : b = 1 - a := by linarith
          subst hb_eq
          nlinarith
      intro z hz
      exact h_le hz
    · rintro y ⟨hyP, hymax⟩
      rw [Set.mem_singleton_iff]
      have hly : l x ≤ l y := hymax x hx_in_P
      rw [hP_eq] at hyP
      let Vfin := hV0_fin.toFinset
      have hVfin : (Vfin : Set (Fin d → ℝ)) = V0 := hV0_fin.coe_toFinset
      rw [← hVfin] at hyP
      obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.mp hyP
      have h_sum_nonneg : ∀ s ∈ Vfin, 0 ≤ w s * (l x - l s) := by
        intro s hs
        refine mul_nonneg (hw0 s hs) ?_
        by_cases hsx : s = x
        · subst hsx; linarith
        · have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
          have hls := hlu s (subset_convexHull ℝ _ hs_diff)
          linarith
      have h_sum_le : ∑ s ∈ Vfin, w s * (l x - l s) ≤ 0 := by
        have h_eq : ∑ s ∈ Vfin, w s * (l x - l s) = l x - l (∑ s ∈ Vfin, w s • s) := by
          rw [map_sum]
          simp_rw [map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
            hw1, one_mul]
        linarith
      have h_all_zero : ∀ s ∈ Vfin, w s * (l x - l s) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg h_sum_nonneg).mp
          (le_antisymm h_sum_le (Finset.sum_nonneg h_sum_nonneg))
      have hw_zero_of_ne : ∀ s ∈ Vfin, s ≠ x → w s = 0 := by
        intro s hs hsx
        have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
        have hls := (hlu s (subset_convexHull ℝ _ hs_diff)).trans hux
        have h_z := h_all_zero s hs
        rcases mul_eq_zero.mp h_z with hw_z | hl_z
        · exact hw_z
        · linarith
      calc ∑ s ∈ Vfin, w s • s
          = ∑ s ∈ Vfin, w s • x := by
            refine Finset.sum_congr rfl (fun s hs => ?_)
            by_cases hsx : s = x
            · subst hsx; rfl
            · simp [hw_zero_of_ne s hs hsx]
        _ = (∑ s ∈ Vfin, w s) • x := (Finset.sum_smul).symm
        _ = x := by rw [hw1, one_smul]
  · intro x hx
    exact exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hx)

theorem polytope_face_eq_convexHull_exposed_vertices_sr_sr (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ F : PolytopeFace P,
        F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := by
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hExtEq : P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
    extremePoints_eq_exposedSingletons_sr P hP
  have hVertFin : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite := by
    rw [← hExtEq, hP_eq]
    exact hV0_fin.subset extremePoints_convexHull_subset
  refine ⟨hVertFin, ?_⟩
  intro F
  have hP_comp : IsCompact P := hP_eq ▸ hV0_fin.isCompact_convexHull ℝ
  have hP_conv : Convex ℝ P := hP_eq ▸ convex_convexHull ℝ V0
  have hF_comp : IsCompact F.val := F.property.isCompact hP_comp
  have hF_conv : Convex ℝ F.val := F.property.convex hP_conv
  have hF_ext : F.val.extremePoints ℝ = F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
    rw [F.property.isExtreme.extremePoints_eq, ← hExtEq]
  have h_km := closure_convexHull_extremePoints hF_comp hF_conv
  rw [hF_ext] at h_km
  have h_closed : IsClosed (convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) :=
    ((hVertFin.subset Set.inter_subset_right).isCompact_convexHull ℝ).isClosed
  rw [h_closed.closure_eq] at h_km
  exact h_km.symm

noncomputable def schemeVertSet {d k : ℕ} {P : Set (Fin d → ℝ)}
    (V : Fin k → (Fin d → ℝ)) (F : PolytopeFace P) : Finset ℕ :=
  by
    classical
    exact (Finset.univ.filter (fun i : Fin k => V i ∈ F.val)).map ⟨Fin.val, Fin.val_injective⟩

theorem coe_schemeVertSet {d k : ℕ} {P : Set (Fin d → ℝ)}
    (V : Fin k → (Fin d → ℝ)) (F : PolytopeFace P) :
    (schemeVertSet V F : Set ℕ) = {n : ℕ | ∃ i : Fin k, i.val = n ∧ V i ∈ F.val} := by
  classical
  ext n
  simp [schemeVertSet, and_comm]

theorem schemeVertSet_le_iff {d k : ℕ} {P : Set (Fin d → ℝ)}
    (hPd : IsDPolytope P)
    (V : Fin k → (Fin d → ℝ)) (hV_range : Set.range V = {x | IsExposed ℝ P {x}})
    (F₁ F₂ : PolytopeFace P) :
    F₁ ≤ F₂ ↔ schemeVertSet V F₁ ⊆ schemeVertSet V F₂ := by
  constructor
  · intro hle n hn
    rw [ ← Finset.mem_coe, coe_schemeVertSet ] at hn ⊢
    rcases hn with ⟨i, rfl, hi⟩
    exact ⟨i, rfl, hle hi⟩
  · intro hsub
    have hHull := (polytope_face_eq_convexHull_exposed_vertices_sr_sr d P hPd).2 F₁
    rw [← hV_range] at hHull
    obtain ⟨⟨Vset, _, _, hPhull⟩, _⟩ := hPd
    have hF2_conv : Convex ℝ F₂.val := by
      refine F₂.2.convex ?_
      rw [hPhull]
      exact convex_convexHull ℝ _
    change F₁.val ⊆ F₂.val
    rw [hHull]
    refine convexHull_min ?_ hF2_conv
    rintro x ⟨hxF1, i, rfl⟩
    have hi1 : i.val ∈ (schemeVertSet V F₁ : Set ℕ) := by
      rw [coe_schemeVertSet]
      exact ⟨i, rfl, hxF1⟩
    have hi2 : i.val ∈ (schemeVertSet V F₂ : Set ℕ) := hsub hi1
    rw [coe_schemeVertSet] at hi2
    rcases hi2 with ⟨j, hj, hjF2⟩
    have hij : j = i := Fin.ext hj
    subst hij
    exact hjF2

theorem mem_range_schemeVertSet_iff {d k : ℕ} {P : Set (Fin d → ℝ)} {S : List (List ℕ)}
    (V : Fin k → (Fin d → ℝ)) (hV_range : Set.range V = {x | IsExposed ℝ P {x}})
    (hS : ∀ J : Finset ℕ,
      (∃ L ∈ S, L.toFinset = J) ↔
        ∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
          (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F})
    (J : Finset ℕ) :
    (∃ F : PolytopeFace P, schemeVertSet V F = J) ↔
      J = ∅ ∨ J = Finset.range k ∨ (∃ L ∈ S, L.toFinset = J) := by
  have hVP : ∀ i : Fin k, V i ∈ P := by
    intro i
    have hVi : V i ∈ Set.range V := Set.mem_range_self i
    rw [hV_range] at hVi
    exact hVi.subset (Set.mem_singleton (V i))
  have hTopSet : ({n : ℕ | ∃ i : Fin k, i.val = n ∧ V i ∈ P} : Set ℕ) =
      (Finset.range k : Set ℕ) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
    constructor
    · rintro ⟨i, rfl, _⟩
      exact i.isLt
    · intro hn
      exact ⟨⟨n, hn⟩, rfl, hVP ⟨n, hn⟩⟩
  constructor
  · rintro ⟨F, rfl⟩
    rcases F.val.eq_empty_or_nonempty with hEmp | hNe
    · left
      rw [← Finset.coe_inj, coe_schemeVertSet, hEmp]
      simp
    · by_cases hFP : F.val = P
      · right; left
        rw [← Finset.coe_inj, coe_schemeVertSet, hFP, hTopSet]
      · right; right
        rw [hS]
        exact ⟨F.val, F.2, hNe, hFP, coe_schemeVertSet V F⟩
  · rintro (rfl | rfl | hLS)
    · refine ⟨⟨∅, fun h => (Set.not_nonempty_empty h).elim⟩, ?_⟩
      rw [← Finset.coe_inj, coe_schemeVertSet]
      simp
    · refine ⟨⟨P, fun _ => ⟨0, by simp⟩⟩, ?_⟩
      rw [← Finset.coe_inj, coe_schemeVertSet, hTopSet]
    · obtain ⟨Fset, hFe, _, _, hJeq⟩ := (hS J).mp hLS
      refine ⟨⟨Fset, hFe⟩, ?_⟩
      rw [← Finset.coe_inj, coe_schemeVertSet, hJeq]

theorem schemeRealizes_unique_combinatorial_type (d₁ d₂ k : ℕ) (S : List (List ℕ))
    (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
    (hP : SchemeRealizes k S P) (hQ : SchemeRealizes k S Q) :
    Nonempty (PolytopeFace P ≃o PolytopeFace Q) := by
  classical
  rcases hP with ⟨hPd, VP, _, hVP_range, hSP⟩
  rcases hQ with ⟨hQd, VQ, _, hVQ_range, hSQ⟩
  have hFwd : ∀ F : PolytopeFace P, ∃ G : PolytopeFace Q,
      schemeVertSet VQ G = schemeVertSet VP F := by
    intro F
    rw [mem_range_schemeVertSet_iff VQ hVQ_range hSQ,
      ← mem_range_schemeVertSet_iff VP hVP_range hSP]
    exact ⟨F, rfl⟩
  have hBwd : ∀ G : PolytopeFace Q, ∃ F : PolytopeFace P,
      schemeVertSet VP F = schemeVertSet VQ G := by
    intro G
    rw [mem_range_schemeVertSet_iff VP hVP_range hSP,
      ← mem_range_schemeVertSet_iff VQ hVQ_range hSQ]
    exact ⟨G, rfl⟩
  let toFun : PolytopeFace P → PolytopeFace Q := fun F => Classical.choose (hFwd F)
  have htoFun : ∀ F : PolytopeFace P, schemeVertSet VQ (toFun F) = schemeVertSet VP F :=
    fun F => Classical.choose_spec (hFwd F)
  let invFun : PolytopeFace Q → PolytopeFace P := fun G => Classical.choose (hBwd G)
  have hinvFun : ∀ G : PolytopeFace Q, schemeVertSet VP (invFun G) = schemeVertSet VQ G :=
    fun G => Classical.choose_spec (hBwd G)
  have hLeft : Function.LeftInverse invFun toFun := by
    intro F
    apply le_antisymm
    · rw [schemeVertSet_le_iff hPd VP hVP_range, hinvFun, htoFun]
    · rw [schemeVertSet_le_iff hPd VP hVP_range, hinvFun, htoFun]
  have hRight : Function.RightInverse invFun toFun := by
    intro G
    apply le_antisymm
    · rw [schemeVertSet_le_iff hQd VQ hVQ_range, htoFun, hinvFun]
    · rw [schemeVertSet_le_iff hQd VQ hVQ_range, htoFun, hinvFun]
  exact ⟨{
    toFun := toFun
    invFun := invFun
    left_inv := hLeft
    right_inv := hRight
    map_rel_iff' := by
      intro F₁ F₂
      change toFun F₁ ≤ toFun F₂ ↔ F₁ ≤ F₂
      rw [schemeVertSet_le_iff hQd VQ hVQ_range, htoFun, htoFun,
        ← schemeVertSet_le_iff hPd VP hVP_range]
  }⟩

end Grunbaum2003

namespace Grunbaum2003

theorem exposedFace_eq_convexHull_incident_range {d n : ℕ}
    (v : Fin n → Fin d → ℝ) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) :
    F = convexHull ℝ (F ∩ Set.range v) := by
  have hPcomp : IsCompact (convexHull ℝ (Set.range v)) :=
    (Set.finite_range v).isCompact_convexHull ℝ
  have hFcomp : IsCompact F := hF.isCompact hPcomp
  have hFconv : Convex ℝ F := hF.convex (convex_convexHull ℝ (Set.range v))
  have hExtRange : F.extremePoints ℝ ⊆ Set.range v := by
    intro x hx
    rw [hF.isExtreme.extremePoints_eq] at hx
    exact extremePoints_convexHull_subset hx.2
  have hExtFin : (F.extremePoints ℝ).Finite := (Set.finite_range v).subset hExtRange
  have hKM := closure_convexHull_extremePoints hFcomp hFconv
  rw [(hExtFin.isCompact_convexHull ℝ).isClosed.closure_eq] at hKM
  apply Set.Subset.antisymm
  · apply hKM.symm.subset.trans
    apply convexHull_mono
    intro x hx
    exact ⟨extremePoints_subset hx, hExtRange hx⟩
  · exact convexHull_min Set.inter_subset_left hFconv

theorem exposedFace_subset_iff_incident_labels {d n : ℕ}
    (v : Fin n → Fin d → ℝ) {F G : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F)
    (hG : IsExposed ℝ (convexHull ℝ (Set.range v)) G) :
    F ⊆ G ↔ ∀ i : Fin n, v i ∈ F → v i ∈ G := by
  constructor
  · intro h i hi
    exact h hi
  · intro h
    rw [exposedFace_eq_convexHull_incident_range v hF,
      exposedFace_eq_convexHull_incident_range v hG]
    apply convexHull_mono
    rintro x ⟨hx, i, rfl⟩
    exact ⟨h i hx, ⟨i, rfl⟩⟩

theorem exposedFace_of_label_maximizers {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (s : Set (Fin n)) (hs : s.Nonempty)
    (l : (Fin d → ℝ) →L[ℝ] ℝ) (b : ℝ)
    (hbound : ∀ i : Fin n, l (v i) ≤ b)
    (heq : ∀ i : Fin n, l (v i) = b ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' s)) ∧
      ∀ i : Fin n, v i ∈ convexHull ℝ (v '' s) ↔ i ∈ s := by
  let P := convexHull ℝ (Set.range v)
  let F := l.toExposed P
  have hPbound : ∀ x ∈ P, l x ≤ b := by
    have hconv : Convex ℝ {x : Fin d → ℝ | l x ≤ b} := by
      intro x hx y hy a c ha hc hac
      change l (a • x + c • y) ≤ b
      rw [map_add, map_smul, map_smul]
      change a * l x + c * l y ≤ b
      calc a * l x + c * l y ≤ a * b + c * b :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hc)
        _ = b := by rw [← add_mul, hac, one_mul]
    exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hbound i) hconv
  have hFlabels : ∀ i : Fin n, v i ∈ F ↔ i ∈ s := by
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := hs
      have hbj : l (v j) = b := (heq j).mpr hj
      have hbi : b ≤ l (v i) := by
        rw [← hbj]
        exact hi.2 (v j) (subset_convexHull ℝ _ (Set.mem_range_self j))
      exact (heq i).mp (le_antisymm (hbound i) hbi)
    · intro hi
      refine ⟨subset_convexHull ℝ _ (Set.mem_range_self i), ?_⟩
      intro x hx
      rw [(heq i).mpr hi]
      exact hPbound x hx
  have hInc : F ∩ Set.range v = v '' s := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, (hFlabels i).mp hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hFlabels i).mpr hi, Set.mem_range_self i⟩
  have hFhull : F = convexHull ℝ (v '' s) := by
    calc F = convexHull ℝ (F ∩ Set.range v) :=
          exposedFace_eq_convexHull_incident_range v
            (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
      _ = convexHull ℝ (v '' s) := congrArg (convexHull ℝ) hInc
  constructor
  · rw [← hFhull]
    exact (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
  · intro i
    rw [← hFhull]
    exact hFlabels i

theorem exposedFaces_orderIso_of_incidence_certificate {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (family : Finset (Finset (Fin n)))
    (hSound : ∀ F : Set (Fin d → ℝ),
      IsExposed ℝ (convexHull ℝ (Set.range v)) F →
      ∀ s : Finset (Fin n), (∀ i : Fin n, i ∈ s ↔ v i ∈ F) → s ∈ family)
    (hComplete : ∀ s ∈ family,
      IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (s : Set (Fin n)))) ∧
        ∀ i : Fin n, v i ∈ convexHull ℝ (v '' (s : Set (Fin n))) ↔ i ∈ s) :
    Nonempty ({F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ≃o
      ↥family) := by
  classical
  let f : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ↪o ↥family := {
    toFun := fun F => ⟨Finset.univ.filter (fun i => v i ∈ F.val),
      hSound F.val F.property _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and])⟩
    inj' := by
      intro F G h
      have hfg : (Finset.univ.filter fun i => v i ∈ F.val) =
          (Finset.univ.filter fun i => v i ∈ G.val) := congrArg Subtype.val h
      have hi : ∀ i : Fin n, v i ∈ F.val ↔ v i ∈ G.val := by
        intro i
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.ext_iff.mp hfg i)
      apply Subtype.ext
      apply Set.Subset.antisymm
      · exact (exposedFace_subset_iff_incident_labels v F.property G.property).mpr
          (fun i hv => (hi i).mp hv)
      · exact (exposedFace_subset_iff_incident_labels v G.property F.property).mpr
          (fun i hv => (hi i).mpr hv)
    map_rel_iff' := by
      intro F G
      change (Finset.univ.filter (fun i => v i ∈ F.val)) ⊆
        (Finset.univ.filter (fun i => v i ∈ G.val)) ↔ F.val ⊆ G.val
      simpa only [Finset.subset_iff, Finset.mem_filter,
        Finset.mem_univ, true_and] using
        (exposedFace_subset_iff_incident_labels v F.property G.property).symm }
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨convexHull ℝ (v '' (s.val : Set (Fin n))), (hComplete s.val s.property).1⟩, ?_⟩
    apply Subtype.ext
    ext i
    change i ∈ Finset.univ.filter (fun i => v i ∈ convexHull ℝ (v '' (s.val : Set (Fin n)))) ↔
      i ∈ s.val
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hComplete s.val s.property).2 i
  exact ⟨OrderIso.ofSurjective f hf⟩

theorem exposedFaces_orderIso_of_incidence_certificate_with_incidence {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (family : Finset (Finset (Fin n)))
    (hSound : ∀ F : Set (Fin d → ℝ),
      IsExposed ℝ (convexHull ℝ (Set.range v)) F →
      ∀ s : Finset (Fin n), (∀ i : Fin n, i ∈ s ↔ v i ∈ F) → s ∈ family)
    (hComplete : ∀ s ∈ family,
      IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (s : Set (Fin n)))) ∧
        ∀ i : Fin n, v i ∈ convexHull ℝ (v '' (s : Set (Fin n))) ↔ i ∈ s) :
    ∃ Φ : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ≃o ↥family,
      ∀ F i, i ∈ (Φ F).val ↔ v i ∈ F.val := by
  classical
  let f : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ↪o ↥family := {
    toFun := fun F => ⟨Finset.univ.filter (fun i => v i ∈ F.val),
      hSound F.val F.property _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and])⟩
    inj' := by
      intro F G h
      have hfg : (Finset.univ.filter fun i => v i ∈ F.val) =
          (Finset.univ.filter fun i => v i ∈ G.val) := congrArg Subtype.val h
      have hi : ∀ i : Fin n, v i ∈ F.val ↔ v i ∈ G.val := by
        intro i
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.ext_iff.mp hfg i)
      apply Subtype.ext
      apply Set.Subset.antisymm
      · exact (exposedFace_subset_iff_incident_labels v F.property G.property).mpr
          (fun i hv => (hi i).mp hv)
      · exact (exposedFace_subset_iff_incident_labels v G.property F.property).mpr
          (fun i hv => (hi i).mpr hv)
    map_rel_iff' := by
      intro F G
      change (Finset.univ.filter (fun i => v i ∈ F.val)) ⊆
        (Finset.univ.filter (fun i => v i ∈ G.val)) ↔ F.val ⊆ G.val
      simpa only [Finset.subset_iff, Finset.mem_filter,
        Finset.mem_univ, true_and] using
        (exposedFace_subset_iff_incident_labels v F.property G.property).symm }
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨convexHull ℝ (v '' (s.val : Set (Fin n))), (hComplete s.val s.property).1⟩, ?_⟩
    apply Subtype.ext
    ext i
    change i ∈ Finset.univ.filter (fun i => v i ∈ convexHull ℝ (v '' (s.val : Set (Fin n)))) ↔
      i ∈ s.val
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hComplete s.val s.property).2 i
  refine ⟨OrderIso.ofSurjective f hf, ?_⟩
  intro F i
  change i ∈ Finset.univ.filter (fun i => v i ∈ F.val) ↔ v i ∈ F.val
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Grunbaum2003

open scoped BigOperators

namespace Grunbaum2003

noncomputable section

private def supportFunctional {d : ℕ} (a : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun x => ∑ t, a t * x t
     map_add' := by
       intro x y
       simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
     map_smul' := by
       intro c x
       simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
       exact Finset.sum_congr rfl (fun t _ => mul_left_comm (a t) c (x t))
    } : (Fin d → ℝ) →ₗ[ℝ] ℝ).toContinuousLinearMap

private theorem supportFunctional_apply {d : ℕ} (a x : Fin d → ℝ) :
    supportFunctional a x = ∑ t, a t * x t := rfl

private theorem exists_support_coefficients {d : ℕ} (l : (Fin d → ℝ) →L[ℝ] ℝ) :
    ∃ a : Fin d → ℝ, ∀ x : Fin d → ℝ, l x = ∑ t, a t * x t := by
  refine ⟨fun t => l (fun j => if t = j then 1 else 0), ?_⟩
  intro x
  simpa only [ContinuousLinearMap.coe_coe, smul_eq_mul, mul_comm] using l.toLinearMap.pi_apply_eq_sum_univ x

theorem incidence_set_eq_iff {d k : ℕ} (V : Fin k → Fin d → ℝ)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range k) (F : Set (Fin d → ℝ)) :
    (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F} ↔
      ∀ i : Fin k, V i ∈ F ↔ i.val ∈ J := by
  constructor
  · intro h i
    constructor
    · intro hi
      have hn : i.val ∈ (J : Set ℕ) := by rw [h]; exact ⟨i, rfl, hi⟩
      exact hn
    · intro hi
      have hn : i.val ∈ (J : Set ℕ) := hi
      rw [h] at hn
      obtain ⟨j, hji, hjF⟩ := hn
      have hji' : j = i := Fin.ext hji
      exact hji' ▸ hjF
  · intro h
    ext n
    constructor
    · intro hn
      have hnk : n < k := Finset.mem_range.mp (hJ hn)
      exact ⟨⟨n, hnk⟩, rfl, (h ⟨n, hnk⟩).mpr hn⟩
    · rintro ⟨i, rfl, hi⟩
      exact (h i).mp hi

theorem proper_face_incidence_iff_support_coefficients {d k : ℕ}
    (V : Fin k → Fin d → ℝ) (P : Set (Fin d → ℝ))
    (hPgen : P = convexHull ℝ (Set.range V))
    (J : Finset ℕ) (hJ : J ⊆ Finset.range k) (hJne : J.Nonempty)
    (hJproper : J ≠ Finset.range k) :
    (∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
      (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F}) ↔
    ∃ (a : Fin d → ℝ) (b : ℝ),
      (∀ i : Fin k, (∑ t, a t * V i t) ≤ b) ∧
      (∀ i : Fin k, (∑ t, a t * V i t) = b ↔ i.val ∈ J) := by
  have hVP (i : Fin k) : V i ∈ P := by rw [hPgen]; exact subset_convexHull ℝ _ (Set.mem_range_self i)
  constructor
  · rintro ⟨F, hF, hFne, hFproper, hInc⟩
    have hAt := (incidence_set_eq_iff V J hJ F).mp hInc
    obtain ⟨n, hn⟩ := hJne
    let i : Fin k := ⟨n, Finset.mem_range.mp (hJ hn)⟩
    have hiF : V i ∈ F := (hAt i).mpr hn
    obtain ⟨l, hl⟩ := hF hFne
    have hiMax : V i ∈ P ∧ ∀ x ∈ P, l x ≤ l (V i) := by
      simpa only [hl, Set.mem_ofPred_eq] using hiF
    obtain ⟨a, ha⟩ := exists_support_coefficients l
    refine ⟨a, l (V i), ?_, ?_⟩
    · intro j
      rw [← ha]
      exact hiMax.2 (V j) (hVP j)
    · intro j
      rw [← ha]
      constructor
      · intro hj
        apply (hAt j).mp
        rw [hl]
        exact ⟨hVP j, by rw [hj]; exact hiMax.2⟩
      · intro hj
        have hjF := (hAt j).mpr hj
        rw [hl] at hjF
        exact le_antisymm (hiMax.2 _ (hVP j)) (hjF.2 _ (hVP i))
  · rintro ⟨a, b, hbound, heq⟩
    let s : Set (Fin k) := {i | i.val ∈ J}
    have hs : s.Nonempty := by
      obtain ⟨n, hn⟩ := hJne
      exact ⟨⟨n, Finset.mem_range.mp (hJ hn)⟩, hn⟩
    obtain ⟨hF, hAt⟩ := exposedFace_of_label_maximizers V s hs
      (supportFunctional a) b (by simpa only [supportFunctional_apply] using hbound)
        (by simpa only [supportFunctional_apply, s, Set.mem_ofPred_eq] using heq)
    let F := convexHull ℝ (V '' s)
    have hFne : F.Nonempty := hs.image V |>.convexHull
    have hInc : (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F} :=
      (incidence_set_eq_iff V J hJ F).mpr hAt
    refine ⟨F, hPgen ▸ hF, hFne, ?_, hInc⟩
    intro hFP
    apply hJproper
    apply Finset.Subset.antisymm hJ
    intro n hn
    let i : Fin k := ⟨n, Finset.mem_range.mp hn⟩
    apply (hAt i).mp
    change V i ∈ F
    rw [hFP]
    exact hVP i

theorem proper_face_incidence_bounds {d k : ℕ}
    (V : Fin k → Fin d → ℝ) (P : Set (Fin d → ℝ))
    (hPgen : P = convexHull ℝ (Set.range V))
    (J : Finset ℕ) (F : Set (Fin d → ℝ))
    (hF : IsExposed ℝ P F) (hFne : F.Nonempty) (hFP : F ≠ P)
    (hInc : (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F}) :
    J ⊆ Finset.range k ∧ J.Nonempty ∧ J ≠ Finset.range k := by
  have hJ : J ⊆ Finset.range k := by
    intro n hn
    have hn' : n ∈ (J : Set ℕ) := hn
    rw [hInc] at hn'
    obtain ⟨i, rfl, _⟩ := hn'
    exact Finset.mem_range.mpr i.isLt
  have hAt := (incidence_set_eq_iff V J hJ F).mp hInc
  have hF' : IsExposed ℝ (convexHull ℝ (Set.range V)) F := hPgen ▸ hF
  have hFhull := exposedFace_eq_convexHull_incident_range V (F := F) hF'
  have hIncNe : (F ∩ Set.range V).Nonempty :=
    convexHull_nonempty_iff.mp (hFhull ▸ hFne)
  obtain ⟨_, hxF, i, rfl⟩ := hIncNe
  refine ⟨hJ, ⟨i.val, (hAt i).mp hxF⟩, ?_⟩
  intro hJall
  apply hFP
  apply Set.Subset.antisymm hF.subset
  rw [hPgen]
  apply convexHull_min ?_ (hF.convex (by rw [hPgen]; exact convex_convexHull ℝ _))
  rintro _ ⟨j, rfl⟩
  apply (hAt j).mpr
  rw [hJall]
  exact Finset.mem_range.mpr j.isLt

theorem singleton_exposed_iff_strict_support_coefficients {d k : ℕ}
    (V : Fin k → Fin d → ℝ) (P : Set (Fin d → ℝ))
    (hPgen : P = convexHull ℝ (Set.range V)) (hV : Function.Injective V) (i : Fin k) :
    IsExposed ℝ P {V i} ↔
      ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * V j t) < ∑ t, a t * V i t := by
  have hVP (j : Fin k) : V j ∈ P := by
    rw [hPgen]
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  constructor
  · intro hi
    obtain ⟨l, hl⟩ := hi (Set.singleton_nonempty (V i))
    have hiMax : ∀ x ∈ P, l x ≤ l (V i) := by
      have hVi : V i ∈ ({V i} : Set (Fin d → ℝ)) := Set.mem_singleton _
      rw [hl] at hVi
      exact hVi.2
    obtain ⟨a, ha⟩ := exists_support_coefficients l
    refine ⟨a, ?_⟩
    intro j hji
    rw [← ha, ← ha]
    apply lt_of_le_of_ne (hiMax _ (hVP j))
    intro heq
    have hjF : V j ∈ ({V i} : Set (Fin d → ℝ)) := by
      rw [hl]
      refine ⟨hVP j, ?_⟩
      rw [heq]
      exact hiMax
    exact hji (hV (Set.mem_singleton_iff.mp hjF))
  · rintro ⟨a, ha⟩
    have hbound : ∀ j : Fin k, supportFunctional a (V j) ≤ supportFunctional a (V i) := by
      intro j
      rw [supportFunctional_apply, supportFunctional_apply]
      by_cases hji : j = i
      · rw [hji]
      · exact (ha j hji).le
    have heq : ∀ j : Fin k,
        supportFunctional a (V j) = supportFunctional a (V i) ↔ j ∈ ({i} : Set (Fin k)) := by
      intro j
      rw [supportFunctional_apply, supportFunctional_apply]
      change _ ↔ j = i
      constructor
      · intro h
        by_contra hji
        exact (ne_of_lt (ha j hji)) h
      · intro hji
        rw [hji]
    have h := (exposedFace_of_label_maximizers V ({i} : Set (Fin k))
      (Set.singleton_nonempty i) (supportFunctional a) (supportFunctional a (V i)) hbound heq).1
    rw [hPgen]
    simpa only [Set.image_singleton, convexHull_singleton] using h

theorem exists_schemeRealizes_iff_finite_support_certificates (d k : ℕ)
    (S : List (List ℕ)) :
    (∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ↔
    ∃ V : Fin k → Fin d → ℝ,
      0 < k ∧ Function.Injective V ∧ affineSpan ℝ (Set.range V) = ⊤ ∧
      (∀ i : Fin k, ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * V j t) < ∑ t, a t * V i t) ∧
      (∀ L ∈ S, ∀ n ∈ L, n < k) ∧
      ∀ J ∈ (Finset.range k).powerset,
        (∃ L ∈ S, L.toFinset = J) ↔
          J.Nonempty ∧ J ≠ Finset.range k ∧
            ∃ (a : Fin d → ℝ) (b : ℝ),
              (∀ i : Fin k, (∑ t, a t * V i t) ≤ b) ∧
              (∀ i : Fin k, (∑ t, a t * V i t) = b ↔ i.val ∈ J) := by
  classical
  constructor
  · rintro ⟨P, hP, V, hV, hRange, hFaces⟩
    have hVP : Set.range V ⊆ P := by
      intro x hx
      rw [hRange] at hx
      exact hx.subset (Set.mem_singleton x)
    have hPgen : P = convexHull ℝ (Set.range V) := by
      have h := (polytope_face_eq_convexHull_exposed_vertices_sr d P hP).2 ⟨P, IsExposed.refl P⟩
      rw [← hRange, Set.inter_eq_right.mpr hVP] at h
      exact h
    have hPne : P.Nonempty := by
      obtain ⟨W, _, hWne, hPW⟩ := hP.1
      rw [hPW]
      exact hWne.convexHull
    have hVne : (Set.range V).Nonempty := convexHull_nonempty_iff.mp (hPgen ▸ hPne)
    obtain ⟨_, i, rfl⟩ := hVne
    refine ⟨V, lt_of_le_of_lt (Nat.zero_le i.val) i.isLt, hV, ?_, ?_, ?_, ?_⟩
    · rw [← affineSpan_convexHull, ← hPgen]
      exact hP.2
    · intro j
      apply (singleton_exposed_iff_strict_support_coefficients V P hPgen hV j).mp
      have hj : V j ∈ Set.range V := Set.mem_range_self j
      rw [hRange] at hj
      exact hj
    · intro L hL n hn
      obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces L.toFinset).mp ⟨L, hL, rfl⟩
      have hBounds := proper_face_incidence_bounds V P hPgen L.toFinset F hF hFne hFP hInc
      exact Finset.mem_range.mp (hBounds.1 (List.mem_toFinset.mpr hn))
    · intro J hJpow
      have hJ : J ⊆ Finset.range k := Finset.mem_powerset.mp hJpow
      constructor
      · intro hJS
        obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces J).mp hJS
        have hBounds := proper_face_incidence_bounds V P hPgen J F hF hFne hFP hInc
        refine ⟨hBounds.2.1, hBounds.2.2, ?_⟩
        exact (proper_face_incidence_iff_support_coefficients V P hPgen J hJ
          hBounds.2.1 hBounds.2.2).mp ⟨F, hF, hFne, hFP, hInc⟩
      · rintro ⟨hJne, hJproper, hCert⟩
        exact (hFaces J).mpr ((proper_face_incidence_iff_support_coefficients V P hPgen J
          hJ hJne hJproper).mpr hCert)
  · rintro ⟨V, hk, hV, hSpan, hVertices, hBound, hRows⟩
    let P := convexHull ℝ (Set.range V)
    have hP : IsDPolytope P := by
      refine ⟨⟨Set.range V, Set.finite_range V,
        ⟨V ⟨0, hk⟩, ⟨⟨0, hk⟩, rfl⟩⟩, rfl⟩, ?_⟩
      rw [affineSpan_convexHull]
      exact hSpan
    have hVertex (i : Fin k) : IsExposed ℝ P {V i} :=
      (singleton_exposed_iff_strict_support_coefficients V P rfl hV i).mpr (hVertices i)
    have hRange : Set.range V = {x | IsExposed ℝ P {x}} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact hVertex i
      · intro hx
        have hExt := exposedPoints_subset_extremePoints
          (mem_exposedPoints_iff_exposed_singleton.mpr hx)
        exact extremePoints_convexHull_subset hExt
    refine ⟨P, hP, V, hV, hRange, ?_⟩
    intro J
    by_cases hJ : J ⊆ Finset.range k
    · constructor
      · intro hJS
        obtain ⟨hJne, hJproper, hCert⟩ := (hRows J (Finset.mem_powerset.mpr hJ)).mp hJS
        exact (proper_face_incidence_iff_support_coefficients V P rfl J hJ hJne hJproper).mpr hCert
      · rintro ⟨F, hF, hFne, hFP, hInc⟩
        have hBounds := proper_face_incidence_bounds V P rfl J F hF hFne hFP hInc
        apply (hRows J (Finset.mem_powerset.mpr hJ)).mpr
        exact ⟨hBounds.2.1, hBounds.2.2,
          (proper_face_incidence_iff_support_coefficients V P rfl J hJ
            hBounds.2.1 hBounds.2.2).mp ⟨F, hF, hFne, hFP, hInc⟩⟩
    · constructor
      · rintro ⟨L, hLS, rfl⟩
        apply False.elim
        apply hJ
        intro n hn
        exact Finset.mem_range.mpr (hBound L hLS n (List.mem_toFinset.mp hn))
      · rintro ⟨F, hF, hFne, hFP, hInc⟩
        exact (hJ (proper_face_incidence_bounds V P rfl J F hF hFne hFP hInc).1).elim

end
end Grunbaum2003

namespace Grunbaum2003

theorem face_orderIso_empty_iff {d e : ℕ} {P : Set (Fin d → ℝ)}
    {Q : Set (Fin e → ℝ)} (φ : PolytopeFace P ≃o PolytopeFace Q)
    (F : PolytopeFace P) : (φ F).val = ∅ ↔ F.val = ∅ := by
  constructor
  · intro h
    have hle : φ F ≤ φ ⟨∅, isExposed_empty⟩ := by
      change (φ F).val ⊆ _
      rw [h]
      exact Set.empty_subset _
    exact Set.Subset.antisymm ((φ.le_iff_le).mp hle) (Set.empty_subset _)
  · intro h
    have hle : F ≤ φ.symm ⟨∅, isExposed_empty⟩ := by
      change F.val ⊆ _
      rw [h]
      exact Set.empty_subset _
    have hle' := φ.monotone hle
    rw [φ.apply_symm_apply] at hle'
    exact Set.Subset.antisymm hle' (Set.empty_subset _)

theorem face_orderIso_nonempty_iff {d e : ℕ} {P : Set (Fin d → ℝ)}
    {Q : Set (Fin e → ℝ)} (φ : PolytopeFace P ≃o PolytopeFace Q)
    (F : PolytopeFace P) : (φ F).val.Nonempty ↔ F.val.Nonempty := by
  simpa only [Set.nonempty_iff_ne_empty] using not_congr (face_orderIso_empty_iff φ F)

theorem face_orderIso_full_iff {d e : ℕ} {P : Set (Fin d → ℝ)}
    {Q : Set (Fin e → ℝ)} (φ : PolytopeFace P ≃o PolytopeFace Q)
    (F : PolytopeFace P) : (φ F).val = Q ↔ F.val = P := by
  let topP : PolytopeFace P := ⟨P, IsExposed.refl P⟩
  let topQ : PolytopeFace Q := ⟨Q, IsExposed.refl Q⟩
  have hTop : φ topP = topQ := by
    apply le_antisymm
    · exact (φ topP).property.subset
    · have hle : φ.symm topQ ≤ topP := (φ.symm topQ).property.subset
      have hle' := φ.monotone hle
      rwa [φ.apply_symm_apply] at hle'
  constructor
  · intro h
    have hEq : φ F = topQ := Subtype.ext h
    exact congrArg Subtype.val (φ.injective (hEq.trans hTop.symm))
  · intro h
    have hEq : F = topP := Subtype.ext h
    rw [hEq, hTop]

theorem face_orderIso_singleton_image {d e : ℕ} {P : Set (Fin d → ℝ)}
    {Q : Set (Fin e → ℝ)} (hQ : IsDPolytope Q)
    (φ : PolytopeFace P ≃o PolytopeFace Q) (x : Fin d → ℝ)
    (hx : IsExposed ℝ P {x}) :
    ∃ y : Fin e → ℝ, IsExposed ℝ Q {y} ∧ (φ ⟨{x}, hx⟩).val = {y} := by
  let X : PolytopeFace P := ⟨{x}, hx⟩
  have hNe : (φ X).val.Nonempty :=
    (face_orderIso_nonempty_iff φ X).mpr (Set.singleton_nonempty x)
  have hHull := (polytope_face_eq_convexHull_exposed_vertices_sr e Q hQ).2 (φ X)
  have hIncNe : ((φ X).val ∩ {y | IsExposed ℝ Q {y}}).Nonempty :=
    convexHull_nonempty_iff.mp (hHull ▸ hNe)
  obtain ⟨y, hyF, hy⟩ := hIncNe
  let Y : PolytopeFace Q := ⟨{y}, hy⟩
  have hYX : Y ≤ φ X := Set.singleton_subset_iff.mpr hyF
  have hPre : φ.symm Y ≤ X := by
    have h := φ.symm.monotone hYX
    rwa [φ.symm_apply_apply] at h
  have hPreNe : (φ.symm Y).val.Nonempty := by
    apply (face_orderIso_nonempty_iff φ (φ.symm Y)).mp
    rw [φ.apply_symm_apply]
    exact Set.singleton_nonempty y
  obtain ⟨z, hz⟩ := hPreNe
  have hzx : z = x := Set.mem_singleton_iff.mp (hPre hz)
  have hxPre : x ∈ (φ.symm Y).val := hzx ▸ hz
  have hPreEq : φ.symm Y = X := by
    apply Subtype.ext
    exact Set.Subset.antisymm hPre (Set.singleton_subset_iff.mpr hxPre)
  refine ⟨y, hy, ?_⟩
  have hImage : φ X = Y := by rw [← hPreEq, φ.apply_symm_apply]
  exact congrArg Subtype.val hImage

theorem face_orderIso_vertex_permutation {d e k : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)} (hQ : IsDPolytope Q)
    (p : Fin k → Fin d → ℝ) (q : Fin k → Fin e → ℝ)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpRange : Set.range p = {x | IsExposed ℝ P {x}})
    (hqRange : Set.range q = {x | IsExposed ℝ Q {x}})
    (φ : PolytopeFace P ≃o PolytopeFace Q) :
    ∃ σ : Equiv.Perm (Fin k), ∀ (F : PolytopeFace P) (i : Fin k),
      p i ∈ F.val ↔ q (σ i) ∈ (φ F).val := by
  classical
  have hpEx (i : Fin k) : IsExposed ℝ P {p i} := by
    have h : p i ∈ Set.range p := Set.mem_range_self i
    rw [hpRange] at h
    exact h
  have hMap : ∀ i : Fin k, ∃ j : Fin k, (φ ⟨{p i}, hpEx i⟩).val = {q j} := by
    intro i
    obtain ⟨y, hy, hImage⟩ := face_orderIso_singleton_image hQ φ (p i) (hpEx i)
    have hyRange : y ∈ Set.range q := hqRange.symm ▸ hy
    obtain ⟨j, rfl⟩ := hyRange
    exact ⟨j, hImage⟩
  choose f hf using hMap
  have hfInj : Function.Injective f := by
    intro i j hij
    apply hp
    have hImage : φ ⟨{p i}, hpEx i⟩ = φ ⟨{p j}, hpEx j⟩ := by
      apply Subtype.ext
      rw [hf i, hf j, hij]
    exact Set.singleton_injective (congrArg Subtype.val (φ.injective hImage))
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective f ⟨hfInj, Finite.surjective_of_injective hfInj⟩
  refine ⟨σ, ?_⟩
  intro F i
  have h := φ.map_rel_iff (a := ⟨{p i}, hpEx i⟩) (b := F)
  change (φ ⟨{p i}, hpEx i⟩).val ⊆ (φ F).val ↔ {p i} ⊆ F.val at h
  rw [hf i] at h
  dsimp only [σ, Equiv.ofBijective]
  simpa only [Set.singleton_subset_iff, Equiv.coe_fn_mk] using h.symm

end Grunbaum2003

namespace Grunbaum2003

theorem schemeRealizes_face_orderIso_code {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (h : SchemeRealizes k S P) :
    Nonempty (PolytopeFace P ≃o
      {J : Finset ℕ // J = ∅ ∨ J = Finset.range k ∨ ∃ L ∈ S, L.toFinset = J}) := by
  classical
  obtain ⟨hP, V, hV, hRange, hFaces⟩ := h
  let f : PolytopeFace P ↪o
      {J : Finset ℕ // J = ∅ ∨ J = Finset.range k ∨ ∃ L ∈ S, L.toFinset = J} := {
    toFun := fun F => ⟨schemeVertSet V F,
      (mem_range_schemeVertSet_iff V hRange hFaces _).mp ⟨F, rfl⟩⟩
    inj' := by
      intro F G hFG
      have hEq := congrArg Subtype.val hFG
      apply le_antisymm
      · exact (schemeVertSet_le_iff hP V hRange F G).mpr (le_of_eq hEq)
      · exact (schemeVertSet_le_iff hP V hRange G F).mpr (le_of_eq hEq.symm)
    map_rel_iff' := by
      intro F G
      exact (schemeVertSet_le_iff hP V hRange F G).symm }
  have hf : Function.Surjective f := by
    intro J
    obtain ⟨F, hF⟩ := (mem_range_schemeVertSet_iff V hRange hFaces J.val).mpr J.property
    exact ⟨F, Subtype.ext hF⟩
  exact ⟨OrderIso.ofSurjective f hf⟩

end Grunbaum2003

namespace Grunbaum2003

private theorem val_mem_finset_map {k : ℕ} (J : Finset (Fin k)) (i : Fin k) :
    i.val ∈ J.map Fin.valEmbedding ↔ i ∈ J := by
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    exact (Fin.ext hji) ▸ hj
  · intro hi
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

private theorem perm_mem_finset_map {k : ℕ} (σ : Equiv.Perm (Fin k))
    (J : Finset (Fin k)) (i : Fin k) : σ i ∈ J.map σ.toEmbedding ↔ i ∈ J := by
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    exact (σ.injective hji) ▸ hj
  · intro hi
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

private theorem val_map_subset_range {k : ℕ} (J : Finset (Fin k)) :
    J.map Fin.valEmbedding ⊆ Finset.range k := by
  intro n hn
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hn
  exact Finset.mem_range.mpr i.isLt

private theorem scheme_row_transport {d e k : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (p : Fin k → Fin d → ℝ) (q : Fin k → Fin e → ℝ)
    (S T : List (List ℕ)) (φ : PolytopeFace P ≃o PolytopeFace Q)
    (σ : Equiv.Perm (Fin k))
    (hInc : ∀ (F : PolytopeFace P) (i : Fin k), p i ∈ F.val ↔ q (σ i) ∈ (φ F).val)
    (hS : ∀ J : Finset ℕ, (∃ L ∈ S, L.toFinset = J) ↔
      ∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
        (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ p i ∈ F})
    (hT : ∀ J : Finset ℕ, (∃ L ∈ T, L.toFinset = J) ↔
      ∃ G : Set (Fin e → ℝ), IsExposed ℝ Q G ∧ G.Nonempty ∧ G ≠ Q ∧
        (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ q i ∈ G})
    (J : Finset (Fin k)) :
    (∃ L ∈ S, L.toFinset = J.map Fin.valEmbedding) →
      ∃ L ∈ T, L.toFinset = (J.map σ.toEmbedding).map Fin.valEmbedding := by
  intro hJS
  obtain ⟨F, hF, hFne, hFproper, hNat⟩ := (hS _).mp hJS
  let X : PolytopeFace P := ⟨F, hF⟩
  have hAt := (incidence_set_eq_iff p _ (val_map_subset_range J) F).mp hNat
  have hTarget : ∀ j : Fin k,
      q j ∈ (φ X).val ↔ j.val ∈ (J.map σ.toEmbedding).map Fin.valEmbedding := by
    intro j
    obtain ⟨i, rfl⟩ := σ.surjective j
    calc
      q (σ i) ∈ (φ X).val ↔ p i ∈ X.val := (hInc X i).symm
      _ ↔ i.val ∈ J.map Fin.valEmbedding := hAt i
      _ ↔ i ∈ J := val_mem_finset_map J i
      _ ↔ σ i ∈ J.map σ.toEmbedding := (perm_mem_finset_map σ J i).symm
      _ ↔ (σ i).val ∈ (J.map σ.toEmbedding).map Fin.valEmbedding :=
        (val_mem_finset_map (J.map σ.toEmbedding) (σ i)).symm
  apply (hT _).mpr
  exact ⟨(φ X).val, (φ X).property,
    (face_orderIso_nonempty_iff φ X).mpr hFne,
    fun h => hFproper ((face_orderIso_full_iff φ X).mp h),
    (incidence_set_eq_iff q _ (val_map_subset_range (J.map σ.toEmbedding)) (φ X).val).mpr hTarget⟩

theorem schemeRealizes_normalized_rows_permutation {d e k : ℕ}
    {S T : List (List ℕ)} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hSP : SchemeRealizes k S P) (hTQ : SchemeRealizes k T Q)
    (φ : PolytopeFace P ≃o PolytopeFace Q) :
    ∃ σ : Equiv.Perm (Fin k), ∀ J : Finset (Fin k),
      (∃ L ∈ S, L.toFinset = J.map Fin.valEmbedding) ↔
        (∃ L ∈ T, L.toFinset = (J.map σ.toEmbedding).map Fin.valEmbedding) := by
  classical
  obtain ⟨hP, p, hp, hpRange, hS⟩ := hSP
  obtain ⟨hQ, q, hq, hqRange, hT⟩ := hTQ
  obtain ⟨σ, hInc⟩ := face_orderIso_vertex_permutation hQ p q hp hq hpRange hqRange φ
  have hInv : ∀ (G : PolytopeFace Q) (j : Fin k),
      q j ∈ G.val ↔ p (σ.symm j) ∈ (φ.symm G).val := by
    intro G j
    simpa only [φ.apply_symm_apply, σ.apply_symm_apply] using
      (hInc (φ.symm G) (σ.symm j)).symm
  refine ⟨σ, ?_⟩
  intro J
  constructor
  · exact scheme_row_transport p q S T φ σ hInc hS hT J
  · intro hJT
    have hJS := scheme_row_transport q p T S φ.symm σ.symm hInv hT hS
      (J.map σ.toEmbedding) hJT
    have hBack : (J.map σ.toEmbedding).map σ.symm.toEmbedding = J := by
      ext i
      have h := (perm_mem_finset_map σ.symm (J.map σ.toEmbedding) (σ i)).trans
        (perm_mem_finset_map σ J i)
      simpa only [σ.symm_apply_apply] using h
    simpa only [hBack] using hJS

end Grunbaum2003

namespace Grunbaum2003

def incidenceRows (k : ℕ) (S : List (List ℕ)) : List (List ℕ) :=
  ((List.range k).sublists').filter (fun R =>
    R = [] ∨ R = List.range k ∨ ∃ L ∈ S, L.toFinset = R.toFinset)

def incidenceMatrix (k : ℕ) (S : List (List ℕ)) : List (List Bool) :=
  (incidenceRows k S).map (fun A => (incidenceRows k S).map (fun B => decide (A ⊆ B)))

private theorem primrec_incidence_sublists {A : Type} [Primcodable A] :
    Primrec (@List.sublists' A) := by
  have hFold : Primrec (fun l : List A => l.foldr (fun a r => r ++ r.map (List.cons a)) [[]]) := by
    apply Primrec.list_foldr
      (h := fun (_ : List A) (p : A × List (List A)) => p.2 ++ p.2.map (List.cons p.1))
      Primrec.id (Primrec.const [[]])
    change Primrec (fun p : List A × (A × List (List A)) =>
      p.2.2 ++ p.2.2.map (List.cons p.2.1))
    exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  apply hFold.of_eq
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.sublists'_cons, ih]

private theorem primrec_nat_mem_list : PrimrecRel (fun n : ℕ => fun L : List ℕ => n ∈ L) :=
  PrimrecRel.of_eq Primrec.eq.exists_mem_list.swap (by intro n L; simp)

private theorem primrec_list_subset_sr : PrimrecRel (fun A B : List ℕ => A ⊆ B) :=
  PrimrecRel.of_eq primrec_nat_mem_list.forall_mem_list (by intro A B; rfl)

private theorem primrec_row_set_eq : PrimrecRel (fun A B : List ℕ => A.toFinset = B.toFinset) := by
  have hBoth : PrimrecRel (fun A B : List ℕ => A ⊆ B ∧ B ⊆ A) := by
    change PrimrecPred (fun p : List ℕ × List ℕ => p.1 ⊆ p.2 ∧ p.2 ⊆ p.1)
    exact primrec_list_subset_sr.and primrec_list_subset_sr.swap
  apply PrimrecRel.of_eq hBoth
  intro A B
  constructor
  · rintro ⟨hAB, hBA⟩
    apply Finset.Subset.antisymm
    · intro n hn
      exact List.mem_toFinset.mpr (hAB (List.mem_toFinset.mp hn))
    · intro n hn
      exact List.mem_toFinset.mpr (hBA (List.mem_toFinset.mp hn))
  · intro h
    constructor
    · intro n hn
      have hn' : n ∈ A.toFinset := List.mem_toFinset.mpr hn
      rw [h] at hn'
      exact List.mem_toFinset.mp hn'
    · intro n hn
      have hn' : n ∈ B.toFinset := List.mem_toFinset.mpr hn
      rw [← h] at hn'
      exact List.mem_toFinset.mp hn'

theorem primrec_incidenceRows : Primrec₂ incidenceRows := by
  have hTest : PrimrecRel (fun p : ℕ × List (List ℕ) => fun R : List ℕ =>
      R = [] ∨ R = List.range p.1 ∨ ∃ L ∈ p.2, L.toFinset = R.toFinset) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const [])).or
      ((Primrec.eq.comp Primrec.snd (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))).or
        (primrec_row_set_eq.exists_mem_list.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  have hRows : Primrec (fun p : ℕ × List (List ℕ) => (List.range p.1).sublists') :=
    primrec_incidence_sublists.comp (Primrec.list_range.comp Primrec.fst)
  exact (hTest.swap.listFilter.comp hRows Primrec.id).to₂

theorem primrec_incidenceMatrix : Primrec₂ incidenceMatrix := by
  have hRows : Primrec (fun p : ℕ × List (List ℕ) => incidenceRows p.1 p.2) := primrec_incidenceRows
  have hInner : Primrec (fun t : (ℕ × List (List ℕ)) × List ℕ =>
      (incidenceRows t.1.1 t.1.2).map (fun B => decide (t.2 ⊆ B))) :=
    Primrec.list_map (hRows.comp Primrec.fst)
      (primrec_list_subset_sr.decide.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map hRows hInner.to₂).to₂

theorem mem_incidenceRows_iff (k : ℕ) (S : List (List ℕ)) (R : List ℕ) :
    R ∈ incidenceRows k S ↔ R.Sublist (List.range k) ∧
      (R = [] ∨ R = List.range k ∨ ∃ L ∈ S, L.toFinset = R.toFinset) := by
  simp only [incidenceRows, List.mem_filter, List.mem_sublists', decide_eq_true_eq]

theorem incidenceRows_nodup (k : ℕ) (S : List (List ℕ)) : (incidenceRows k S).Nodup :=
  (List.nodup_sublists'.mpr (List.nodup_range : (List.range k).Nodup)).filter _

theorem incidenceRows_toFinset_injective (k : ℕ) (S : List (List ℕ))
    {R T : List ℕ} (hR : R ∈ incidenceRows k S) (hT : T ∈ incidenceRows k S)
    (hEq : R.toFinset = T.toFinset) : R = T := by
  have hRs := ((mem_incidenceRows_iff k S R).mp hR).1
  have hTs := ((mem_incidenceRows_iff k S T).mp hT).1
  have hRn : R.Nodup := (List.nodup_range : (List.range k).Nodup).sublist hRs
  have hTn : T.Nodup := (List.nodup_range : (List.range k).Nodup).sublist hTs
  have hPerm : R.Perm T := by
    have h := List.toFinset_eq_iff_perm_dedup.mp hEq
    simpa only [hRn.dedup, hTn.dedup] using h
  exact ((List.nodup_range : (List.range k).Nodup).perm_iff_eq_of_sublist hRs hTs).mp hPerm

theorem schemeRealizes_rows_bounded {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (h : SchemeRealizes k S P) :
    ∀ L ∈ S, ∀ n ∈ L, n < k := by
  obtain ⟨hP, V, hV, hRange, hFaces⟩ := h
  intro L hL n hn
  obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces L.toFinset).mp ⟨L, hL, rfl⟩
  have hn' : n ∈ (L.toFinset : Set ℕ) := List.mem_toFinset.mpr hn
  rw [hInc] at hn'
  obtain ⟨i, hi, _⟩ := hn'
  exact hi ▸ i.isLt

theorem incidenceRows_toFinset_iff (k : ℕ) (S : List (List ℕ))
    (hBound : ∀ L ∈ S, ∀ n ∈ L, n < k) (J : Finset ℕ) :
    (∃ R ∈ incidenceRows k S, R.toFinset = J) ↔
      J = ∅ ∨ J = Finset.range k ∨ ∃ L ∈ S, L.toFinset = J := by
  constructor
  · rintro ⟨R, hR, rfl⟩
    rcases ((mem_incidenceRows_iff k S R).mp hR).2 with hnil | hfull | hrow
    · left
      rw [hnil]
      rfl
    · right; left
      rw [hfull]
      exact List.toFinset_range k
    · exact Or.inr (Or.inr hrow)
  · rintro (rfl | rfl | ⟨L, hL, rfl⟩)
    · refine ⟨[], (mem_incidenceRows_iff k S []).mpr ⟨List.nil_sublist _, Or.inl rfl⟩, rfl⟩
    · refine ⟨List.range k, (mem_incidenceRows_iff k S _).mpr ⟨List.Sublist.refl _, Or.inr (Or.inl rfl)⟩,
        List.toFinset_range k⟩
    · let R := (List.range k).filter (fun n => n ∈ L)
      have hEq : R.toFinset = L.toFinset := by
        ext n
        simp only [List.mem_toFinset, R, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨And.right, fun hn => ⟨hBound L hL n hn, hn⟩⟩
      refine ⟨R, (mem_incidenceRows_iff k S R).mpr ⟨List.filter_sublist,
        Or.inr (Or.inr ⟨L, hL, hEq.symm⟩)⟩, hEq⟩

end Grunbaum2003

namespace Grunbaum2003

private theorem list_subset_iff_finset_subset (A B : List ℕ) :
    A ⊆ B ↔ A.toFinset ⊆ B.toFinset := by
  constructor
  · intro h n hn
    exact List.mem_toFinset.mpr (h (List.mem_toFinset.mp hn))
  · intro h n hn
    exact List.mem_toFinset.mp (h (List.mem_toFinset.mpr hn))

theorem schemeRealizes_rows_equiv_faces {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (hP : SchemeRealizes k S P) :
    ∃ e : Fin (incidenceRows k S).length ≃ PolytopeFace P,
      ∀ i j, ((incidenceRows k S).get i ⊆ (incidenceRows k S).get j) ↔ e i ≤ e j := by
  classical
  let rows := incidenceRows k S
  let C := {J : Finset ℕ // J = ∅ ∨ J = Finset.range k ∨ ∃ L ∈ S, L.toFinset = J}
  have hBound := schemeRealizes_rows_bounded hP
  let f : Fin rows.length → C := fun i => ⟨(rows.get i).toFinset,
    (incidenceRows_toFinset_iff k S hBound _).mp ⟨rows.get i, List.get_mem rows i, rfl⟩⟩
  have hfInj : Function.Injective f := by
    intro i j hij
    apply (incidenceRows_nodup k S).injective_get
    exact incidenceRows_toFinset_injective k S (List.get_mem rows i) (List.get_mem rows j)
      (congrArg Subtype.val hij)
  have hfSurj : Function.Surjective f := by
    intro J
    obtain ⟨R, hR, hSet⟩ := (incidenceRows_toFinset_iff k S hBound J.val).mpr J.property
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hR
    refine ⟨i, Subtype.ext ?_⟩
    change (rows.get i).toFinset = J.val
    rw [hi]
    exact hSet
  let ec : Fin rows.length ≃ C := Equiv.ofBijective f ⟨hfInj, hfSurj⟩
  obtain ⟨Φ⟩ := schemeRealizes_face_orderIso_code hP
  let e : Fin rows.length ≃ PolytopeFace P := ec.trans Φ.symm.toEquiv
  have he (i : Fin rows.length) : (Φ (e i)).val = (rows.get i).toFinset := by
    have hFace : Φ (e i) = ec i := by
      change Φ (Φ.symm (ec i)) = ec i
      exact Φ.apply_symm_apply (ec i)
    rw [hFace]
    exact congrArg Subtype.val (congrFun (Equiv.coe_ofBijective f ⟨hfInj, hfSurj⟩) i)
  refine ⟨e, ?_⟩
  intro i j
  rw [list_subset_iff_finset_subset]
  have h := Φ.le_iff_le (x := e i) (y := e j)
  change (Φ (e i)).val ⊆ (Φ (e j)).val ↔ e i ≤ e j at h
  rw [he i, he j] at h
  exact h

@[simp] theorem incidenceMatrix_length (k : ℕ) (S : List (List ℕ)) :
    (incidenceMatrix k S).length = (incidenceRows k S).length := by
  simp only [incidenceMatrix, List.length_map]

theorem incidenceMatrix_entry (k : ℕ) (S : List (List ℕ))
    (i j : Fin (incidenceMatrix k S).length) :
    (((incidenceMatrix k S).get i)[j.val]?).getD false =
      decide ((incidenceRows k S).get (finCongr (incidenceMatrix_length k S) i) ⊆
        (incidenceRows k S).get (finCongr (incidenceMatrix_length k S) j)) := by
  have hi : i.val < (incidenceRows k S).length := by
    simpa only [incidenceMatrix_length] using i.isLt
  have hj : j.val < (incidenceRows k S).length := by
    simpa only [incidenceMatrix_length] using j.isLt
  change (((incidenceRows k S).map (fun A =>
      (incidenceRows k S).map (fun B => decide (A ⊆ B))))[i.val]'(by
        simpa only [List.length_map] using hi))[j.val]?.getD false =
    decide ((incidenceRows k S)[i.val]'hi ⊆ (incidenceRows k S)[j.val]'hj)
  rw [List.getElem_map, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

theorem schemeRealizes_matrix_equiv_faces {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (hP : SchemeRealizes k S P) :
    ∃ e : Fin (incidenceMatrix k S).length ≃ PolytopeFace P,
      ∀ i j, (((incidenceMatrix k S).get i)[j.val]?).getD false = true ↔ e i ≤ e j := by
  obtain ⟨er, hr⟩ := schemeRealizes_rows_equiv_faces hP
  let ec := finCongr (incidenceMatrix_length k S)
  refine ⟨ec.trans er, ?_⟩
  intro i j
  rw [incidenceMatrix_entry, decide_eq_true_eq]
  simpa only [Equiv.trans_apply] using hr (ec i) (ec j)

end Grunbaum2003

namespace Grunbaum2003

theorem schemeRealizes_transfer_of_face_orderIso {d e k : ℕ}
    {S T : List (List ℕ)} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hSP : SchemeRealizes k S P) (hTQ : SchemeRealizes k T Q)
    (φ : PolytopeFace P ≃o PolytopeFace Q) : SchemeRealizes k T P := by
  classical
  obtain ⟨hP, p, hp, hpRange, hSFaces⟩ := hSP
  obtain ⟨hQ, q, hq, hqRange, hTFaces⟩ := hTQ
  obtain ⟨σ, hInc⟩ := face_orderIso_vertex_permutation hQ p q hp hq hpRange hqRange φ
  let v : Fin k → Fin d → ℝ := p ∘ σ.symm
  have hv : Function.Injective v := hp.comp σ.symm.injective
  have hvRange : Set.range v = {x | IsExposed ℝ P {x}} := by
    rw [show Set.range v = Set.range p by
      change Set.range (p ∘ σ.symm) = Set.range p
      rw [Set.range_comp, σ.symm.surjective.range_eq, Set.image_univ]]
    exact hpRange
  have hInc' (F : PolytopeFace P) (j : Fin k) :
      v j ∈ F.val ↔ q j ∈ (φ F).val := by
    simpa only [v, Function.comp_apply, σ.apply_symm_apply] using hInc F (σ.symm j)
  have hLabels (F : PolytopeFace P) :
      {n : ℕ | ∃ j : Fin k, j.val = n ∧ v j ∈ F.val} =
        {n : ℕ | ∃ j : Fin k, j.val = n ∧ q j ∈ (φ F).val} := by
    ext n
    change (∃ j : Fin k, j.val = n ∧ v j ∈ F.val) ↔
      (∃ j : Fin k, j.val = n ∧ q j ∈ (φ F).val)
    simp_rw [hInc' F]
  refine ⟨hP, v, hv, hvRange, ?_⟩
  intro J
  constructor
  · intro hJT
    obtain ⟨G, hG, hGne, hGproper, hJ⟩ := (hTFaces J).mp hJT
    let F : PolytopeFace P := φ.symm ⟨G, hG⟩
    have hFne : F.val.Nonempty := by
      apply (face_orderIso_nonempty_iff φ F).mp
      simpa only [F, φ.apply_symm_apply] using hGne
    have hFproper : F.val ≠ P := by
      intro hFull
      have h := (face_orderIso_full_iff φ F).mpr hFull
      exact hGproper (by simpa only [F, φ.apply_symm_apply] using h)
    refine ⟨F.val, F.property, hFne, hFproper, ?_⟩
    have h : {n : ℕ | ∃ j : Fin k, j.val = n ∧ v j ∈ F.val} =
        {n : ℕ | ∃ j : Fin k, j.val = n ∧ q j ∈ G} := by
      simpa only [F, φ.apply_symm_apply] using hLabels F
    exact hJ.trans h.symm
  · rintro ⟨F, hF, hFne, hFproper, hJ⟩
    let X : PolytopeFace P := ⟨F, hF⟩
    have hGne : (φ X).val.Nonempty := (face_orderIso_nonempty_iff φ X).mpr hFne
    have hGproper : (φ X).val ≠ Q :=
      fun h => hFproper ((face_orderIso_full_iff φ X).mp h)
    exact (hTFaces J).mpr ⟨(φ X).val, (φ X).property, hGne, hGproper,
      hJ.trans (hLabels X)⟩

theorem schemeRealizes_transfer_all_of_face_orderIso {d e r k : ℕ}
    {S T : List (List ℕ)} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hSP : SchemeRealizes k S P) (hTQ : SchemeRealizes k T Q)
    (φ : PolytopeFace P ≃o PolytopeFace Q)
    {R : Set (Fin r → ℝ)} (hSR : SchemeRealizes k S R) : SchemeRealizes k T R := by
  obtain ⟨ψ⟩ := schemeRealizes_unique_combinatorial_type r d k S R P hSR hSP
  exact schemeRealizes_transfer_of_face_orderIso hSR hTQ (ψ.trans φ)

end Grunbaum2003

theorem bounded_scheme_has_candidate (k : ℕ) (S : List (List ℕ))
    (hBound : ∀ L ∈ S, ∀ n ∈ L, n < k) :
    ∃ T ∈ ((List.range k).sublists').sublists',
      ∀ J : Finset ℕ,
        (∃ L ∈ T, L.toFinset = J) ↔ (∃ L ∈ S, L.toFinset = J) := by
  classical
  let rows := (List.range k).sublists'
  let T := rows.filter (fun R => ∃ L ∈ S, L.toFinset = R.toFinset)
  refine ⟨T, List.mem_sublists'.mpr (List.filter_sublist), ?_⟩
  intro J
  constructor
  · rintro ⟨L, hL, rfl⟩
    simpa only [T, List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hL).2
  · rintro ⟨L, hL, rfl⟩
    let R := (List.range k).filter (fun n => n ∈ L)
    have hR : R.toFinset = L.toFinset := by
      ext n
      simp only [List.mem_toFinset, R, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨And.right, fun hn => ⟨hBound L hL n hn, hn⟩⟩
    refine ⟨R, List.mem_filter.mpr ⟨?_, by simpa only [decide_eq_true_eq] using (show ∃ L₀ ∈ S, L₀.toFinset = R.toFinset from ⟨L, hL, hR.symm⟩)⟩, hR⟩
    exact List.mem_sublists'.mpr (List.filter_sublist)

theorem primrec_sublists' {α : Type} [Primcodable α] :
    Primrec (@List.sublists' α) := by
  have hFold : Primrec (fun l : List α =>
      l.foldr (fun a r => r ++ r.map (List.cons a)) [[]]) := by
    apply Primrec.list_foldr (h := fun (_ : List α) (p : α × List (List α)) => p.2 ++ p.2.map (List.cons p.1)) Primrec.id (Primrec.const [[]])
    change Primrec (fun p : List α × (α × List (List α)) =>
      p.2.2 ++ p.2.2.map (List.cons p.2.1))
    exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd))
  apply hFold.of_eq
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.sublists'_cons, ih]

theorem primrec_scheme_candidates : Primrec (fun k : ℕ => ((List.range k).sublists').sublists') :=
  primrec_sublists'.comp (primrec_sublists'.comp Primrec.list_range)

namespace Grunbaum2003

theorem schemeRealizes_has_candidate {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (h : SchemeRealizes k S P) :
    ∃ T ∈ ((List.range k).sublists').sublists',
      ∀ Q : Set (Fin d → ℝ), SchemeRealizes k S Q → SchemeRealizes k T Q := by
  have hBound : ∀ L ∈ S, ∀ n ∈ L, n < k := by
    obtain ⟨hP, V, hV, hRange, hFaces⟩ := h
    intro L hL n hn
    obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces L.toFinset).mp ⟨L, hL, rfl⟩
    have hn' : n ∈ (L.toFinset : Set ℕ) := List.mem_toFinset.mpr hn
    rw [hInc] at hn'
    obtain ⟨i, hi, _⟩ := hn'
    exact hi ▸ i.isLt
  obtain ⟨T, hT, hRows⟩ := bounded_scheme_has_candidate k S hBound
  refine ⟨T, hT, ?_⟩
  rintro Q ⟨hQ, V, hV, hRange, hFaces⟩
  exact ⟨hQ, V, hV, hRange, fun J => (hRows J).trans (hFaces J)⟩

end Grunbaum2003

namespace Grunbaum2003

def schemeTypeIsoCheck (k : ℕ) (S T : List (List ℕ)) : Bool :=
  finiteRelationIsoCheck (incidenceMatrix k S) (incidenceMatrix k T)

theorem primrec_schemeTypeIsoCheck :
    Primrec (fun t : (ℕ × List (List ℕ)) × List (List ℕ) =>
      schemeTypeIsoCheck t.1.1 t.1.2 t.2) :=
  primrec_finiteRelationIsoCheck.comp
    (primrec_incidenceMatrix.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (primrec_incidenceMatrix.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

theorem schemeTypeIsoCheck_equivalence (k : ℕ) :
    Equivalence (fun S T => schemeTypeIsoCheck k S T = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    apply (finiteRelationIsoCheck_eq_true_iff _ _).mpr
    exact ⟨Equiv.refl _, fun _ _ => rfl⟩
  · intro S T h
    obtain ⟨σ, hσ⟩ := (finiteRelationIsoCheck_eq_true_iff _ _).mp h
    apply (finiteRelationIsoCheck_eq_true_iff _ _).mpr
    refine ⟨σ.symm, ?_⟩
    intro i j
    simpa only [σ.apply_symm_apply] using (hσ (σ.symm i) (σ.symm j)).symm
  · intro S T U hST hTU
    obtain ⟨σ, hσ⟩ := (finiteRelationIsoCheck_eq_true_iff _ _).mp hST
    obtain ⟨τ, hτ⟩ := (finiteRelationIsoCheck_eq_true_iff _ _).mp hTU
    apply (finiteRelationIsoCheck_eq_true_iff _ _).mpr
    refine ⟨σ.trans τ, ?_⟩
    intro i j
    simpa only [Equiv.trans_apply] using (hσ i j).trans (hτ (σ i) (σ j))

theorem schemeTypeIsoCheck_iff_face_orderIso {d e k : ℕ}
    {S T : List (List ℕ)} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hSP : SchemeRealizes k S P) (hTQ : SchemeRealizes k T Q) :
    schemeTypeIsoCheck k S T = true ↔ Nonempty (PolytopeFace P ≃o PolytopeFace Q) := by
  classical
  obtain ⟨α, hα⟩ := schemeRealizes_matrix_equiv_faces hSP
  obtain ⟨β, hβ⟩ := schemeRealizes_matrix_equiv_faces hTQ
  rw [schemeTypeIsoCheck, finiteRelationIsoCheck_eq_true_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    let ePQ : PolytopeFace P ≃ PolytopeFace Q := α.symm.trans (σ.trans β)
    refine ⟨{ toEquiv := ePQ, map_rel_iff' := ?_ }⟩
    intro F G
    change ePQ F ≤ ePQ G ↔ F ≤ G
    calc
      ePQ F ≤ ePQ G ↔
          (((incidenceMatrix k T).get (σ (α.symm F)))[(σ (α.symm G)).val]?).getD false = true := by
        simpa only [ePQ, Equiv.trans_apply] using (hβ (σ (α.symm F)) (σ (α.symm G))).symm
      _ ↔ (((incidenceMatrix k S).get (α.symm F))[(α.symm G).val]?).getD false = true := by
        rw [hσ (α.symm F) (α.symm G)]
      _ ↔ F ≤ G := by simpa only [α.apply_symm_apply] using hα (α.symm F) (α.symm G)
  · rintro ⟨φ⟩
    let σ := α.trans (φ.toEquiv.trans β.symm)
    refine ⟨σ, ?_⟩
    intro i j
    apply Bool.eq_iff_iff.mpr
    calc
      (((incidenceMatrix k S).get i)[j.val]?).getD false = true ↔ α i ≤ α j := hα i j
      _ ↔ φ (α i) ≤ φ (α j) := φ.le_iff_le.symm
      _ ↔ β (σ i) ≤ β (σ j) := by
        change (φ (α i) ≤ φ (α j)) ↔
          β (β.symm (φ (α i))) ≤ β (β.symm (φ (α j)))
        rw [β.apply_symm_apply, β.apply_symm_apply]
      _ ↔ (((incidenceMatrix k T).get (σ i))[(σ j).val]?).getD false = true := (hβ (σ i) (σ j)).symm

theorem primrec_scheme_class_prune :
    Primrec₂ (fun k (L : List (List (List ℕ))) =>
      L.pwFilter (fun S T => ¬ schemeTypeIsoCheck k S T = true)) := by
  have hR : PrimrecRel (fun p : ℕ × List (List ℕ) => fun T =>
      ¬ schemeTypeIsoCheck p.1 p.2 T = true) :=
    (Primrec.eq.comp primrec_schemeTypeIsoCheck (Primrec.const true)).not
  exact primrec_parameterized_pwFilter hR

end Grunbaum2003

namespace Grunbaum2003

private def representativeList (D : ℕ → ℕ → List (List ℕ) → Bool) (d k : ℕ) :
    List (List (List ℕ)) :=
  ((((List.range k).sublists').sublists').filter (D d k)).pwFilter
    (fun S T => ¬ schemeTypeIsoCheck k S T = true)

theorem exists_computable_scheme_representatives_of_realizability_decider
    (D : ℕ → ℕ → List (List ℕ) → Bool)
    (hDComp : Computable (fun z : (ℕ × ℕ) × List (List ℕ) => D z.1.1 z.1.2 z.2))
    (hDCorrect : ∀ d k S, D d k S = true ↔
      ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ∧
        (∀ S₀ : List (List ℕ), (∃ P₀ : Set (Fin d → ℝ), SchemeRealizes k S₀ P₀) →
          ∃ S ∈ E d k, ∀ P : Set (Fin d → ℝ),
            SchemeRealizes k S₀ P → SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length, ∀ P Q : Set (Fin d → ℝ),
          SchemeRealizes k ((E d k).get i) P →
          SchemeRealizes k ((E d k).get j) Q →
          Nonempty (PolytopeFace P ≃o PolytopeFace Q) → i = j) := by
  have hCandidates : Computable (fun p : ℕ × ℕ => ((List.range p.2).sublists').sublists') :=
    primrec_scheme_candidates.to_comp.comp Computable.snd
  have hFiltered : Computable (fun p : ℕ × ℕ =>
      (((List.range p.2).sublists').sublists').filter (D p.1 p.2)) :=
    computable_list_filter hCandidates hDComp
  have hE : Computable₂ (representativeList D) :=
    primrec_scheme_class_prune.to_comp.comp Computable.snd hFiltered
  refine ⟨representativeList D, hE, ?_⟩
  intro d k
  let L := (((List.range k).sublists').sublists').filter (D d k)
  have hSub : representativeList D d k ⊆ L := List.pwFilter_subset L
  have hSound : ∀ S ∈ representativeList D d k,
      ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P := by
    intro S hS
    exact (hDCorrect d k S).mp (List.mem_filter.mp (hSub hS)).2
  refine ⟨hSound, ?_, ?_⟩
  · rintro S₀ ⟨P₀, hS₀⟩
    obtain ⟨T, hTmem, hTAll⟩ := schemeRealizes_has_candidate hS₀
    have hT₀ : SchemeRealizes k T P₀ := hTAll P₀ hS₀
    have hTL : T ∈ L := List.mem_filter.mpr
      ⟨hTmem, (hDCorrect d k T).mpr ⟨P₀, hT₀⟩⟩
    obtain ⟨U, hU, hTU⟩ := (pwFilter_complement_covers (schemeTypeIsoCheck_equivalence k) L).2 T hTL
    have hUE : U ∈ representativeList D d k := hU
    obtain ⟨Q, hUQ⟩ := hSound U hUE
    obtain ⟨φ⟩ := (schemeTypeIsoCheck_iff_face_orderIso hT₀ hUQ).mp hTU
    refine ⟨U, hUE, ?_⟩
    intro P hS₀P
    exact schemeRealizes_transfer_all_of_face_orderIso hT₀ hUQ φ (hTAll P hS₀P)
  · intro i j P Q hP hQ hIso
    have hSame := (schemeTypeIsoCheck_iff_face_orderIso hP hQ).mpr hIso
    exact pwFilter_complement_unique_indices (schemeTypeIsoCheck_equivalence k) L i j hSame

end Grunbaum2003

namespace Grunbaum2003

def realizeDecider (d k : ℕ) (S : List (List ℕ)) : Bool :=
  FormulaCompiler.Parametric.decideCodeZero (FormulaCompiler.compile d k S)

theorem computable_realizeDecider :
    Computable (fun z : (ℕ × ℕ) × List (List ℕ) => realizeDecider z.1.1 z.1.2 z.2) :=
  FormulaCompiler.Parametric.computable_decideCodeZero.comp FormulaCompiler.computable_compile

theorem realizeDecider_eq_true_iff (d k : ℕ) (S : List (List ℕ)) :
    realizeDecider d k S = true ↔ ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P := by
  rw [realizeDecider, FormulaCompiler.compile,
    FormulaCompiler.Parametric.decideCodeZero_eq_true_iff_of_code,
    ← FormulaCompiler.compile,
    FormulaCompiler.codeHolds_compile_iff d k S (fun _ => 0)]

theorem auto_GRU_M05_EFFECTIVE_TYPES_exists_computable_realizable_scheme_representatives_sol :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ∧
        (∀ S₀ : List (List ℕ), (∃ P₀ : Set (Fin d → ℝ), SchemeRealizes k S₀ P₀) →
          ∃ S ∈ E d k, ∀ P : Set (Fin d → ℝ), SchemeRealizes k S₀ P → SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length,
          ∀ P Q : Set (Fin d → ℝ),
            SchemeRealizes k ((E d k).get i) P →
            SchemeRealizes k ((E d k).get j) Q →
            Nonempty (PolytopeFace P ≃o PolytopeFace Q) → i = j) :=
  exists_computable_scheme_representatives_of_realizability_decider
    realizeDecider computable_realizeDecider realizeDecider_eq_true_iff

end Grunbaum2003

theorem solution :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), Grunbaum2003.SchemeRealizes k S P) ∧
        (∀ S₀ : List (List ℕ), (∃ P₀ : Set (Fin d → ℝ), Grunbaum2003.SchemeRealizes k S₀ P₀) →
          ∃ S ∈ E d k, ∀ P : Set (Fin d → ℝ), Grunbaum2003.SchemeRealizes k S₀ P → Grunbaum2003.SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length,
          ∀ P Q : Set (Fin d → ℝ),
            Grunbaum2003.SchemeRealizes k ((E d k).get i) P →
            Grunbaum2003.SchemeRealizes k ((E d k).get j) Q →
            Nonempty (Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q) → i = j) :=
  Grunbaum2003.auto_GRU_M05_EFFECTIVE_TYPES_exists_computable_realizable_scheme_representatives_sol
