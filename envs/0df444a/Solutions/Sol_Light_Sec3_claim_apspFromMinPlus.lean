-- Prove2me | solution 1 for Light.Sec3.claim_apspFromMinPlus
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:35:18.413849+00:00
-- url     : https://prove2.me/submissions/26a57a17-a79b-4faf-b038-d8fde1dd1bf6

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_RepeatedSquaring
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSumApsp_Theorem21_entry_le_walkWeight
import Theorems.Thm_ThreeSumApsp_Theorem21_exists_short_walk
import Theorems.Thm_ThreeSumApsp_Theorem21_exists_walk_of_entry

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec

section


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h




























/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩







theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩













/-- Loops.  I i is the invariant before round number i (counted from 0) of n rounds, and b i bounds
the cost of that round. -/
theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      obtain rfl : i = n := by omega
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
      simp only [this] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h
































/-- Calls: verify the body from the frame made of the arguments. -/
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/







/-- The sum of two expressions. -/
infixl:65 " +' " => Expr.op Op.add
/-- The difference of two expressions. -/
infixl:65 " -' " => Expr.op Op.sub
/-- The product of two expressions. -/
infixl:70 " *' " => Expr.op Op.mul
@[inherit_doc] infix:50 " <' " => Cond.lt
@[inherit_doc] infix:50 " =' " => Cond.eq
@[inherit_doc] infixr:30 " ;; " => Stmt.seq



@[inherit_doc] infix:50 " ≤' " => Cond.le








/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame












/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/
























end Light

end
end

section


/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/




































/-! ## The default proofs -/



































/-! ## Rules for blocks -/















































/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ (Light.Stmt.seq s₂ s₃))) σ T Q) : Ends lim P d ((Light.Stmt.seq (Light.Stmt.seq s₁ s₂) s₃)) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d ((Light.Stmt.seq .skip s)) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s .skip)) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  h












































/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
                                                                                                                        |
                                                                                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                                                            (first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega))))
                                                                                                                        | omega
                                                                                                                        |
                                                                                                                          (simp [] <;>
                                                                                                                              first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)

























/-! ## Loops whose body is a block -/














/-! ## Counting loops -/





/-- **Counting loops.**  I j is the invariant before round j.  The bound hi has the value n
throughout, n fits in a word, and the body keeps the counter and takes at most b steps.  The rule
supplies σ.loc i = j; I 0 is asked of σ with 0 in the counter, and I (j + 1) of the state after the
increment. -/
theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
                                                          |
                                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                              (first
                                                                | omega
                                                                | ((ring_nf); (omega))))
                                                          | omega
                                                          |
                                                            (simp [] <;>
                                                                first
                                                                | omega
                                                                | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4) ⟨by simp, by simpa using start⟩
    ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _

/-- **Counting loops whose body changes no local variable.**  Before round j the local variables are
the given ones with j in the counter, and I j holds of the memory.  The bound hi has the value n
throughout, n fits in a word, and the body takes at most b steps. -/
theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ}
    {Q : State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
                                                          |
                                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                              (first
                                                                | omega
                                                                | ((ring_nf); (omega))))
                                                          | omega
                                                          |
                                                            (simp [] <;>
                                                                first
                                                                | omega
                                                                | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

end Light

end
end

section


/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/









/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]











/-! ## The value of an expression -/





/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}














/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT

/-- `mem[a] := e`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ) (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
                                          |
                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                              (first
                                                | omega
                                                | ((ring_nf); (omega))))
                                          | omega
                                          |
                                            (simp [] <;>
                                                first
                                                | omega
                                                | ((ring_nf); (omega)))) :
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

/-- `mem[a] := e ; s`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeToThen {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
                                          |
                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                              (first
                                                | omega
                                                | ((ring_nf); (omega))))
                                          | omega
                                          |
                                            (simp [] <;>
                                                first
                                                | omega
                                                | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.store a e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.storeTo b z h he le_rfl) hT

/-- **Counting loops whose body is a block that changes no local variable**, with the locals as a
list.  Before round j the locals are the given ones with j in the counter, and I j holds of the
memory.  The bound hi gives n, and n fits in a word.  The round is a goal about the body, for the
rules of this file, and its time is body.blockCost, so that no number is typed.  A loop or a call
counts 0 steps in blockCost; for a body that contains one use Ends.forShape. -/
theorem Ends.forFrame {i : ℕ} {hi : Expr} {body : Stmt} (I : ℕ → (ℕ → ℤ) → Prop) (n : ℕ)
    (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal l i j), μ'⟩ body.blockCost fun σ' =>
        σ'.loc = frame (setLocal l i j) ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal l i n), μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal l i j), μ'⟩ n := by intros; (((try have := Light.Std.space_le (by assumption)));
                                                                       ((try have := Light.Std.const_le (by assumption)));
                                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by first
                                                                       |
                                                                         ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                               List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                           (first
                                                                             | omega
                                                                             | ((ring_nf); (omega))))
                                                                       | omega
                                                                       |
                                                                         (simp [] <;>
                                                                             first
                                                                             | omega
                                                                             | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  refine Ends.forMem I n body.blockCost start ?_ ?_ ?_ hn hT
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact round j μ' hj hI
  · intro μ' hI
    rw [update_frame_setLocal]
    exact done μ' hI
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact bound j μ' hj hI


































end rules

/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end

end Light

end
end

section


/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩























end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}

/-- `x := p(args)`, where the arguments give vals.  The procedure runs at depth d + 1. -/
theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                        ((try have := Light.Std.const_le (by assumption)));
                                                                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT











/-- `x := p(args)`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

/-- `x := p(args) ; s`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light

/-! ## Regions -/


















/-! ## Memories that agree on some cells -/























variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}

/-- The case of a single cell. -/
theorem SameOn.cell (h : SameOn (· = b) μ μ') : μ' b = μ b := h b rfl




















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}





/-- Nothing has been written yet. -/
theorem wrote_zero : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]

/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]

/-- One more cell is written. -/
theorem wrote_succ : Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]










/-- Writing `j ≤ n` cells from `dst` changes no cell outside the `n` cells from `dst`. -/
theorem sameOutside_wrote {n : ℕ} (h : j ≤ n) : SameOutside μ (wrote μ dst f j) dst n :=
  fun _ hb => wrote_rest (by omega)

/-! ## The tactics -/









































end Light

end
end

section


/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/

public section

namespace Nat

/-! ## Bounds on an index -/





/-- Row `a < m` ends within the matrix: `a * n + b ≤ m * n` for `b ≤ n`, so also for `b = n`. -/
theorem mul_add_le_mul {a b m n : ℕ} (ha : a < m) (hb : b ≤ n) : a * n + b ≤ m * n :=
  calc a * n + b ≤ a * n + n := Nat.add_le_add_left hb _
    _ = (a + 1) * n := (Nat.succ_mul a n).symm
    _ ≤ m * n := Nat.mul_le_mul_right n ha

/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/












/-- The row of an index below `m * n` is below `m`. -/
theorem div_lt_of_lt_mul' {t m n : ℕ} (h : t < m * n) : t / n < m :=
  Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ h)

/-- The column of an index below `m * n` is below `n`. -/
theorem mod_lt_of_lt_mul {t m n : ℕ} (h : t < m * n) : t % n < n :=
  Nat.mod_lt t (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt h))

/-- Every index below `m * n` is the index of a pair. -/
theorem exists_eq_mul_add_of_lt_mul {t m n : ℕ} (h : t < m * n) : ∃ a < m, ∃ b < n, t = a * n + b :=
  ⟨t / n, div_lt_of_lt_mul' h, t % n, mod_lt_of_lt_mul h, (Nat.div_add_mod' t n).symm⟩

/-- The indices of the diagonal are the multiples of `n + 1`. -/
theorem eq_mul_succ_iff {n i t : ℕ} (hi : i < n) : t = i * (n + 1) ↔ t / n = i ∧ t % n = i := by
  constructor
  · rintro rfl
    rw [Nat.mul_succ]
    exact ⟨mul_add_div_of_lt hi, Nat.mul_add_mod_of_lt hi⟩
  · rintro ⟨hdiv, hmod⟩
    rw [Nat.mul_succ, ← Nat.div_add_mod' t n, hdiv, hmod]

/-! ## The next index -/























end Nat

namespace Int

/-! ## Residues as natural numbers -/










end Int

end
end

section


/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {l : List α} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rwa [List.getD_eq_default l d hi]























































/-! ## Blocks one after the other -/











































































/-! ## Sums -/









































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/












































































/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/














/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end
end

section


/-!
# A pass over an array

`pass c len dst e` is the loop "for c < len: dst[c] := e".  The rule `Ends.pass` says what it does:
if round j computes f j, then the loop writes f 0, …, f (n - 1) to the n cells from dst, changes
nothing else, and takes n (cost of e + 12) + 6 steps.  A routine whose only loop writes cell dst + c
in round c, with the length and dst in local variables, is an instance: its proof only says what
round j reads.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}




variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

/-- After the pass the n cells hold the list of the values f 0, …, f (n - 1). -/
theorem seg_wrote {n : ℕ} {l : List ℤ} (hl : l.length = n)
    (h : ∀ i (hi : i < l.length), l[i] = f i) : Seg (wrote μ dst f n) dst l := fun i hi => by
  rw [wrote_done (hl ▸ hi), h i hi]

/-- A pass that writes g of the entries of a list leaves the list mapped by g. -/
theorem seg_wrote_map (g : ℤ → ℤ) (L : List ℤ) :
    Seg (wrote μ dst (fun i => g (L.getD i 0)) L.length) dst (L.map g) :=
  seg_wrote (List.length_map g) fun i hi => by
    rw [List.getElem_map, List.getD_eq_getElem _ _ (by simpa using hi)]





























end Light

end
end

section


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/






























/-! ## Specifications of single routines -/






/-! ## Tasks and solvers -/



































/-- **A solver meets the specification that its task prescribes**, in every program that begins with
its program. -/
theorem Solves.meets {task : Task} {P₀ : Program} {p : ℕ} {T₀ : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : _root_.Light.Solves task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ} (x : task.Inst) {μ : ℕ → ℤ}
    (fr : ℕ) (hpre : task.Pre x μ fr) (hok : (need (task.size x) (task.bound x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.size x) (task.bound x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩












































/-! ## Hosts -/










/-- From a host to a transfer of running times.  What remains is arithmetic: a bound for the host's
time function, given a bound for the solver's. -/
theorem IsHost.solvedIn {lower upper : Task} {time : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ}
    {need : (ℕ → ℕ → Need) → ℕ → ℕ → Need} (h : IsHost lower upper time need) {T T' : ℕ → ℝ → ℝ}
    (hs : SolvedIn lower T)
    (hb : ∀ Tn : ℕ → ℕ → ℕ, (∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤
    T n u) → ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (time Tn n U : ℝ) ≤ T' n u) :
    SolvedIn upper T' := by
  obtain ⟨P, p, Tn, r, hr, hsol, hT⟩ := hs
  obtain ⟨R, p', hsol'⟩ := h.1 P p Tn r hsol
  exact ⟨P ++ R, p', time Tn, need r, h.2 r hr, hsol', hb Tn hT⟩

/-! ## Tasks with a list of parameters -/














































end Light

end
end

section


/-!
# Bounds up to a constant factor, in several parameters

The paper writes `f = O(g)` for functions of several parameters that are tied by side conditions,
such as `D ^ 18 ≤ n` for the parameters `n`, `D`, `w`. `Dominated dom f g` says this: there is a
constant `C ≥ 0` with `f x ≤ C * g x` for every tuple `x` of parameters that satisfies `dom x`. If
there is no side condition, `dom` is `fun _ => True`. The type `α` of the parameters is best a
structure with one named field for each of them, so that a bound reads
`Dominated (fun p => p.D ^ 18 ≤ p.n) (fun p => cost p) fun p => p.n ^ 2 / p.D`.

The lemmas of this file are the steps that the paper takes without comment: such bounds can be
chained (`Dominated.trans`), added (`Dominated.add`, `Dominated.add_add`), multiplied and divided
(`Dominated.mul`, `Dominated.mul_left`, `Dominated.const_mul`, `Dominated.pow`,
`Dominated.div_right`), joined by a case distinction (`Dominated.ite`), restricted to a smaller
domain (`Dominated.mono_dom`) and specialized (`Dominated.comp`). With them no proof has to name a
constant. A bound enters the calculus by `Dominated.of_le`, `Dominated.of_le_const_mul` or
`Dominated.of_exists_const`, and leaves it by `obtain ⟨C, hC, hle⟩` or `Dominated.exists_const_and`.
For functions of one natural number, `Dominated.of_eventually` takes a bound for all large `n`,
`Dominated.isBigO` gives Mathlib's `f =O[atTop] g`, and `isBigO_comp_add_one` substitutes a size
that need not tend to infinity.

In every closure lemma the bound comes first and the side conditions follow.

For nonnegative `f` and `g` the notion is Mathlib's `f =O[𝓟 {x | dom x}] g`, big-O along the
principal filter of the domain (`dominated_iff_isBigO_principal`). The one-sided form is taken
because a running time is bounded from above only.

## The notions of "bounded up to a constant" in this library

* `f =O[atTop] g` of Mathlib bounds `|f|` for large `n`. In this sense `IsBigOPow f a` is `O(n^a)`,
  `IsPowPolylog f a` is `O(n^a (log n)^e)` for some `e`, and `IsPowLittleO f a` is `n^{a+o(1)}`.
  The exponents of the theorems are stated with them.
* `UpperBigOPow`, `UpperPowPolylog` and `UpperPowLittleO` are the same three classes as bounds on
  `f` and not on `|f|`, for running times. A two-sided bound gives the one-sided one
  (`IsBigOPow.upperBigOPow`, `IsPowPolylog.upperPowPolylog`, `IsPowLittleO.upperPowLittleO`).
* `Dominated dom f g` bounds `f` on the whole domain, for several parameters. It comes from a bound
  for large `n` by `Dominated.of_eventually` and gives one by `Dominated.isBigO`.
* `Scale.SoftO t e` says that a count `t` with values in `ℕ` is `Dominated` by a monomial with the
  exponents `e`, up to powers of one more quantity; the tactic `growth` reads the exponents off an
  explicit expression. It gives a `Dominated` bound by `Scale.SoftO.dominated`. Its instance
  `SoftOSqrtPow` gives `IsPowPolylog` by `SoftOSqrtPow.isPowPolylog`.
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp






namespace Dominated

variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

/-! ### Entering the calculus -/






/-- A bound with constant one. -/
theorem of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g :=
  ⟨1, zero_le_one, fun x hx => by simpa only [one_mul] using hfg x hx⟩






















/-- A constant is `O(g)` when `g ≥ 1` on the domain. -/
protected theorem const (c : ℝ) (hg : ∀ x, dom x → 1 ≤ g x) : Dominated dom (fun _ => c) g :=
  ⟨|c|, abs_nonneg c, fun x hx =>
    (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) (hg x hx))⟩

/-! ### Leaving the calculus -/











/-! ### Chaining, restricting, substituting -/

/-- `f = O(g)` and `g = O(h)` give `f = O(h)`. -/
protected theorem trans (hfg : Dominated dom f g) (hgh : Dominated dom g h) :
    Dominated dom f h := by
  obtain ⟨C, hC, hf⟩ := hfg
  obtain ⟨D, hD, hg⟩ := hgh
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => (hf x hx).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg x hx) hC






/-- The left side may be replaced by a smaller function. -/
theorem mono_left (hfg : Dominated dom f g) (hle : ∀ x, dom x → f' x ≤ f x) : Dominated dom f' g :=
  (of_le hle).trans hfg

/-- The right side may be replaced by a larger function. -/
theorem mono_right (hfg : Dominated dom f g) (hle : ∀ x, dom x → g x ≤ g' x) : Dominated dom f g' :=
  hfg.trans (of_le hle)

/-- Both sides may be replaced by functions that agree with them on the domain. -/
protected theorem congr (hfg : Dominated dom f g) (hf : ∀ x, dom x → f x = f' x)
    (hg : ∀ x, dom x → g x = g' x) : Dominated dom f' g' :=
  (hfg.mono_left fun x hx => (hf x hx).ge).mono_right fun x hx => (hg x hx).le








/-! ### Sums and case distinctions -/

/-- `O(h) + O(h) = O(h)`. -/
protected theorem add (hf : Dominated dom f h) (hg : Dominated dom g h) :
    Dominated dom (fun x => f x + g x) h := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  rw [add_mul]
  exact add_le_add (hf x hx) (hg x hx)






















/-! ### Products and quotients -/






































/-- `O(g₁) · O(g₂) = O(g₁ g₂)` for nonnegative `f₁`, `f₂`. -/
protected theorem mul (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂)
    (hf₁ : ∀ x, dom x → 0 ≤ f₁ x) (hf₂ : ∀ x, dom x → 0 ≤ f₂ x) :
    Dominated dom (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => ?_⟩
  rw [mul_mul_mul_comm]
  exact mul_le_mul (h₁ x hx) (h₂ x hx) (hf₂ x hx) ((hf₁ x hx).trans (h₁ x hx))

/-- `O(g) ^ e = O(g ^ e)` for nonnegative `f`. -/
protected theorem pow (hfg : Dominated dom f g) (hf : ∀ x, dom x → 0 ≤ f x) (e : ℕ) :
    Dominated dom (fun x => f x ^ e) fun x => g x ^ e := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine ⟨C ^ e, pow_nonneg hC e, fun x hx => ?_⟩
  rw [← mul_pow]
  exact pow_le_pow_left₀ (hf x hx) (hle x hx) e

/-! ### Functions of one natural number -/








































end Dominated












end ThreeSumApsp

end
end

section


/-!
# Orders of growth of counts

The time and the need of a program are natural numbers, given by explicit expressions in the
parameters of the input.  Only their order of growth is needed.  This file has one calculus
that reads the order of growth off such an expression, so that no constant is ever written out.

A *scale* (`Scale α ι`) fixes the parameters `x : α` for which bounds are claimed (`dom`) and some
quantities that are at least 1 there: the *bases* `base i`, whose powers are counted, and one more,
`hidden`, whose powers are not.  `s.SoftO t e` says that the count `t` is at most a constant times a
power of `hidden` times the monomial `∏ i, base i ^ e i`.  Three examples:

* bases `n`, `√D`, `κ log n` and `hidden = 1`: `s.SoftO t ![2, 1, 1]` is `t = O(n² √D κ log n)`;
* one base `√n` and `hidden = log n`: `s.SoftO t ![3]` is `t = Õ(n^{3/2})`;
* no base and `hidden = n U`: `s.SoftO t ![]` says that `t` is polynomially bounded.

So `SoftO` is `O` up to powers of `hidden`: it is `O` itself if `hidden = 1`, and `Õ` if `hidden` is
a logarithm.  The bounds hold on the whole domain and not only from some point on.

The exponents follow the expression.  A constant has the exponents 0 (`SoftO.const`), a sum the
larger ones (`SoftO.add`), a product their sum (`SoftO.mul`), a power their multiple (`SoftO.pow`).
Exponents may be raised (`SoftO.mono`), and the count may be replaced by a smaller one
(`SoftO.of_le`, `SoftO.of_forall_le`).  If every base is at most `2 ^ hidden`, the binary logarithm
of a bounded count has the exponents 0 (`SoftO.log2`).

The tactic `growth [h₁, h₂, …]` applies these rules from the outside to the inside of the
expression.  The facts `hᵢ` bound the quantities at which the rules stop: parameters, and functions
whose bound is a lemma of its own.  A function that is to be followed into its definition is
unfolded first.

A bound leaves the calculus by `SoftO.exists_le`, or as a `Dominated` statement by
`SoftO.dominated`.
-/

@[expose] public section

namespace ThreeSumApsp














namespace Scale










variable {α ι : Type*} [Fintype ι] (s : Scale α ι)









theorem mon_zero (x : α) : s.mon 0 x = 1 := by simp [mon]

theorem mon_add (e e' : ι → ℕ) (x : α) : s.mon (e + e') x = s.mon e x * s.mon e' x := by
  simp only [mon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem mon_smul (k : ℕ) (e : ι → ℕ) (x : α) : s.mon (k • e) x = s.mon e x ^ k := by
  simp only [mon, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm k]




variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}

/-- All bases are at least 1, so a monomial grows with its exponents. -/
theorem mon_le_mon (he : ∀ i, e i ≤ e' i) (hx : s.dom x) : s.mon e x ≤ s.mon e' x :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (zero_le_one.trans (s.one_le_base i x hx)) _)
    fun i _ => pow_le_pow_right₀ (s.one_le_base i x hx) (he i)

/-- A monomial is at least 1. -/
theorem one_le_mon (e : ι → ℕ) (hx : s.dom x) : 1 ≤ s.mon e x :=
  (s.mon_zero x).ge.trans (mon_le_mon (fun _ => Nat.zero_le _) hx)

/-- The bound grows with all exponents. -/
theorem pow_mul_mon_le (hc : c ≤ c') (he : ∀ i, e i ≤ e' i) (hx : s.dom x) :
    s.hidden x ^ c * s.mon e x ≤ s.hidden x ^ c' * s.mon e' x :=
  mul_le_mul (pow_le_pow_right₀ (s.one_le_hidden x hx) hc) (mon_le_mon he hx)
    (zero_le_one.trans (one_le_mon e hx)) (pow_nonneg (zero_le_one.trans (s.one_le_hidden x hx)) _)

namespace SoftO

variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}

/-! ### Entering and leaving -/

/-- A count that is at most `hidden`. -/
theorem of_le_hidden (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.hidden x) : s.SoftO t 0 :=
  ⟨1, .of_le fun x hx => by simpa only [pow_one, mon_zero, mul_one] using h x hx⟩















/-- The bound, written out. -/
theorem exists_le (h : s.SoftO t e) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ x, s.dom x → (t x : ℝ) ≤ C * (s.hidden x ^ c * s.mon e x) :=
  let ⟨c, C, hC, hle⟩ := h
  ⟨C, c, hC, hle⟩







/-! ### The rules -/

/-- The exponents may be raised. -/
theorem mono (h : s.SoftO t e) (he : ∀ i, e i ≤ e' i) : s.SoftO t e' :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_right fun _ hx => pow_mul_mon_le le_rfl he hx⟩

/-- A smaller count has the same bound. -/
theorem of_le (h : s.SoftO t₂ e) (hle : ∀ x, s.dom x → t₁ x ≤ t₂ x) : s.SoftO t₁ e :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_left fun x hx => Nat.cast_le.2 (hle x hx)⟩











/-- A constant has the exponents 0. -/
protected theorem const (k : ℕ) : s.SoftO (fun _ => k) 0 :=
  ⟨0, .const _ fun x _ => by rw [pow_zero, mon_zero, mul_one]⟩

/-- A sum has the larger exponents. -/
protected theorem add (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x + t₂ x) (e₁ ⊔ e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨max c₁ c₂, ?_⟩
  simpa only [Nat.cast_add] using
    (h₁.mono_right fun _ hx =>
      pow_mul_mon_le (e' := e₁ ⊔ e₂) (le_max_left _ _) (fun _ => le_sup_left) hx).add
      (h₂.mono_right fun _ hx => pow_mul_mon_le (le_max_right _ _) (fun _ => le_sup_right) hx)





/-- In a product the exponents add up. -/
protected theorem mul (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x * t₂ x) (e₁ + e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨c₁ + c₂, ?_⟩
  simpa only [Nat.cast_mul] using
    (h₁.mul h₂ (fun _ _ => Nat.cast_nonneg _) fun _ _ => Nat.cast_nonneg _).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_add, pow_add, mul_mul_mul_comm]

/-- The `k`-th power multiplies the exponents by `k`. -/
protected theorem pow (h : s.SoftO t e) (k : ℕ) : s.SoftO (fun x => t x ^ k) (k • e) := by
  obtain ⟨c, h⟩ := h
  refine ⟨c * k, ?_⟩
  simpa only [Nat.cast_pow] using
    (h.pow (fun _ _ => Nat.cast_nonneg _) k).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_smul, mul_pow, pow_mul]

/-- A maximum has the larger exponents. -/
protected theorem max (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => max (t₁ x) (t₂ x)) (e₁ ⊔ e₂) :=
  (h₁.add h₂).of_le fun _ _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)















/-- A logarithm is at most the number. -/
protected theorem log (h : s.SoftO t e) (b : ℕ) : s.SoftO (fun x => Nat.log b (t x)) e :=
  h.of_le fun _ _ => Nat.log_le_self _ _

/-- A square root is at most the number. -/
protected theorem sqrt (h : s.SoftO t e) : s.SoftO (fun x => Nat.sqrt (t x)) e :=
  h.of_le fun _ _ => Nat.sqrt_le_self _




































end SoftO

end Scale








































end ThreeSumApsp

end
end

section


/-!
# Polynomially bounded needs

The need of a program is given by explicit expressions in the size n of the input and the bound U on
its numbers.  `PolyBounded F` says that F(n, U) is at most a polynomial in (n + 1)(U + 1).  It is
the calculus `ThreeSumApsp.Scale.SoftO` on the scale `polyScale`, and the tactic `growth_poly`
proves it by following the expression.

Three such functions make a polynomially bounded need (`PolyBounded.polyNeed`), and the need of a
solver that a host calls has three such parts (`PolyNeed.word`, `PolyNeed.cells`, `PolyNeed.depth`).
So the need of a host is polynomially bounded if the need of its solver is; the tactic `poly_need`
proves this from the definition of the need of the host.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Upper bounds that are polynomial in (n + 1)(U + 1) -/













namespace PolyBounded

variable {F : ℕ → ℕ → ℕ}

/-- The size `n` is polynomially bounded. -/
theorem fst : PolyBounded (fun n _ => n) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ p.2.succ_pos)).mono (by decide)

/-- The bound `U` is polynomially bounded. -/
theorem snd : PolyBounded (fun _ U => U) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ p.1.succ_pos)).mono (by decide)

/-- A smaller function has the same bound. -/
theorem of_le {G : ℕ → ℕ → ℕ} (h : PolyBounded G) (hle : ∀ n U, F n U ≤ G n U) : PolyBounded F :=
  Scale.SoftO.of_le h fun _ _ => hle _ _

/-- The bound with natural numbers. -/
theorem exists_nat_le (h : PolyBounded F) :
    ∃ K e : ℕ, ∀ n U, F n U ≤ K * ((n + 1) * (U + 1)) ^ e := by
  obtain ⟨C, e, hC, hle⟩ := h.exists_le
  refine ⟨⌈C⌉₊, e, fun n U => ?_⟩
  have hceil : (F n U : ℝ) ≤ ⌈C⌉₊ * (((n + 1) * (U + 1) : ℕ) : ℝ) ^ e := by
    simpa [polyScale, Scale.mon] using (hle (n, U) trivial).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by simp [polyScale, Scale.mon]; positivity))
  exact_mod_cast hceil

end PolyBounded






namespace PolyBounded

/-- A polynomial bound at polynomially bounded parameters. -/
theorem polyBound {A B : ℕ → ℕ → ℕ} (hA : PolyBounded A) (hB : PolyBounded B) (s k : ℕ) :
    PolyBounded (fun n U => polyBound s k [A n U, B n U]) :=
  of_le (G := fun n U => 2 ^ s * ((A n U + 1) * (B n U + 1)) ^ k) (by first
                                                                      |
                                                                        ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                          (·
                                                                              repeat'
                                                                                with_reducible
                                                                                  first
                                                                                  | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                  | apply Light.PolyBounded.fst
                                                                                  | apply Light.PolyBounded.snd
                                                                                  | apply ThreeSumApsp.Scale.SoftO.log
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                  | apply hA
                                                                                  | apply hB
                                                                                  | apply ThreeSumApsp.Scale.SoftO.add
                                                                                  | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                  | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                  | apply ThreeSumApsp.Scale.SoftO.max
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                  | apply ThreeSumApsp.Scale.SoftO.div);
                                                                          (·
                                                                              first
                                                                              | decide
                                                                              | exact isEmptyElim))
                                                                      |
                                                                        ((fail_if_success
                                                                              (fail_if_success
                                                                                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                                    (on_goal 1 =>
                                                                                        ((repeat'
                                                                                              with_reducible
                                                                                                first
                                                                                                | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                                | apply Light.PolyBounded.fst
                                                                                                | apply Light.PolyBounded.snd
                                                                                                | apply ThreeSumApsp.Scale.SoftO.log
                                                                                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                                | apply hA
                                                                                                | apply hB
                                                                                                | apply ThreeSumApsp.Scale.SoftO.add
                                                                                                | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                                | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                                | apply ThreeSumApsp.Scale.SoftO.max
                                                                                                | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                                | apply ThreeSumApsp.Scale.SoftO.div);
                                                                                          (done))))));
                                                                          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                                                                          (all_goals
                                                                              try
                                                                                ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                                  (·
                                                                                      repeat'
                                                                                        with_reducible
                                                                                          first
                                                                                          | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                          | apply Light.PolyBounded.fst
                                                                                          | apply Light.PolyBounded.snd
                                                                                          | apply ThreeSumApsp.Scale.SoftO.log
                                                                                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                          | apply hA
                                                                                          | apply hB
                                                                                          | apply ThreeSumApsp.Scale.SoftO.add
                                                                                          | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                          | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                          | apply ThreeSumApsp.Scale.SoftO.max
                                                                                          | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                          | apply ThreeSumApsp.Scale.SoftO.div);
                                                                                  (· decide))))
                                                                      |
                                                                        ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                          (·
                                                                              repeat'
                                                                                with_reducible
                                                                                  first
                                                                                  | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                  | apply Light.PolyBounded.fst
                                                                                  | apply Light.PolyBounded.snd
                                                                                  | apply ThreeSumApsp.Scale.SoftO.log
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                  | apply hA
                                                                                  | apply hB
                                                                                  | apply ThreeSumApsp.Scale.SoftO.add
                                                                                  | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                  | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                  | apply ThreeSumApsp.Scale.SoftO.max
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                  | apply ThreeSumApsp.Scale.SoftO.div)))
    fun n U => by simp [Light.polyBound]

/-- Three polynomially bounded functions make a polynomially bounded need. -/
theorem polyNeed {need : ℕ → ℕ → Need} (hw : PolyBounded fun n U => (need n U).word)
    (hc : PolyBounded fun n U => (need n U).cells) (hd : PolyBounded fun n U => (need n U).depth) :
    PolyNeed need := by
  obtain ⟨K, e, hK⟩ := exists_nat_le (F := fun n U => (need n U).word + (need n U).cells +
    (need n U).depth) (by first
                          |
                            ((apply ThreeSumApsp.Scale.SoftO.mono);
                              (·
                                  repeat'
                                    with_reducible
                                      first
                                      | exact ThreeSumApsp.Scale.SoftO.const _
                                      | apply Light.PolyBounded.fst
                                      | apply Light.PolyBounded.snd
                                      | apply ThreeSumApsp.Scale.SoftO.log
                                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                                      | apply hw
                                      | apply hc
                                      | apply hd
                                      | apply ThreeSumApsp.Scale.SoftO.add
                                      | apply ThreeSumApsp.Scale.SoftO.mul
                                      | apply ThreeSumApsp.Scale.SoftO.pow
                                      | apply ThreeSumApsp.Scale.SoftO.max
                                      | apply ThreeSumApsp.Scale.SoftO.sub
                                      | apply ThreeSumApsp.Scale.SoftO.div);
                              (·
                                  first
                                  | decide
                                  | exact isEmptyElim))
                          |
                            ((fail_if_success
                                  (fail_if_success
                                      ((apply ThreeSumApsp.Scale.SoftO.mono);
                                        (on_goal 1 =>
                                            ((repeat'
                                                  with_reducible
                                                    first
                                                    | exact ThreeSumApsp.Scale.SoftO.const _
                                                    | apply Light.PolyBounded.fst
                                                    | apply Light.PolyBounded.snd
                                                    | apply ThreeSumApsp.Scale.SoftO.log
                                                    | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                    | apply hw
                                                    | apply hc
                                                    | apply hd
                                                    | apply ThreeSumApsp.Scale.SoftO.add
                                                    | apply ThreeSumApsp.Scale.SoftO.mul
                                                    | apply ThreeSumApsp.Scale.SoftO.pow
                                                    | apply ThreeSumApsp.Scale.SoftO.max
                                                    | apply ThreeSumApsp.Scale.SoftO.sub
                                                    | apply ThreeSumApsp.Scale.SoftO.div);
                                              (done))))));
                              (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                              (all_goals
                                  try
                                    ((apply ThreeSumApsp.Scale.SoftO.mono);
                                      (·
                                          repeat'
                                            with_reducible
                                              first
                                              | exact ThreeSumApsp.Scale.SoftO.const _
                                              | apply Light.PolyBounded.fst
                                              | apply Light.PolyBounded.snd
                                              | apply ThreeSumApsp.Scale.SoftO.log
                                              | apply ThreeSumApsp.Scale.SoftO.sqrt
                                              | apply hw
                                              | apply hc
                                              | apply hd
                                              | apply ThreeSumApsp.Scale.SoftO.add
                                              | apply ThreeSumApsp.Scale.SoftO.mul
                                              | apply ThreeSumApsp.Scale.SoftO.pow
                                              | apply ThreeSumApsp.Scale.SoftO.max
                                              | apply ThreeSumApsp.Scale.SoftO.sub
                                              | apply ThreeSumApsp.Scale.SoftO.div);
                                      (· decide))))
                          |
                            ((apply ThreeSumApsp.Scale.SoftO.mono);
                              (·
                                  repeat'
                                    with_reducible
                                      first
                                      | exact ThreeSumApsp.Scale.SoftO.const _
                                      | apply Light.PolyBounded.fst
                                      | apply Light.PolyBounded.snd
                                      | apply ThreeSumApsp.Scale.SoftO.log
                                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                                      | apply hw
                                      | apply hc
                                      | apply hd
                                      | apply ThreeSumApsp.Scale.SoftO.add
                                      | apply ThreeSumApsp.Scale.SoftO.mul
                                      | apply ThreeSumApsp.Scale.SoftO.pow
                                      | apply ThreeSumApsp.Scale.SoftO.max
                                      | apply ThreeSumApsp.Scale.SoftO.sub
                                      | apply ThreeSumApsp.Scale.SoftO.div)))
  refine ⟨Nat.size K, e, fun n U => ?_⟩
  have hsum := hK n U
  have hpoly : K * ((n + 1) * (U + 1)) ^ e ≤ Light.polyBound (Nat.size K) e [n, U] := by
    simp only [Light.polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact Nat.mul_le_mul_right _ (Nat.lt_size_self K).le
  exact ⟨by omega, by omega, by omega⟩

end PolyBounded

/-! ## The need of a solver that a host calls

A polynomially bounded need, at a size `A(n, U)` and a bound `B(n, U)` that are polynomially
bounded, has polynomially bounded parts. -/

namespace PolyNeed

variable {need : ℕ → ℕ → Need} {A B : ℕ × ℕ → ℕ} {a b : Fin 0 → ℕ}

private theorem part (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    ∃ R : ℕ → ℕ → ℕ, PolyBounded R ∧ ∀ n U, (need (A (n, U)) (B (n, U))).word ≤ R n U ∧
      (need (A (n, U)) (B (n, U))).cells ≤ R n U ∧ (need (A (n, U)) (B (n, U))).depth ≤ R n U :=
  let ⟨s, k, hle⟩ := h
  ⟨_, PolyBounded.polyBound (A := fun n U => A (n, U)) (B := fun n U => B (n, U))
    (hA.mono isEmptyElim) (hB.mono isEmptyElim) s k, fun _ _ => hle _ _⟩

/-- The numbers of the solver. -/
theorem word (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).word) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).1

/-- The cells of the solver. -/
theorem cells (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).cells) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).2.1

/-- The depth of the calls of the solver. -/
theorem depth (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).depth) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).2.2

end PolyNeed








end Light

end
end

section


/-!
# Theorem 21(b): repeated squaring computes the distances

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix `⌈log₂ n⌉`
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most `nU`, where `U` bounds the edge weights (`theorem_21b_repeated_squaring`,
`theorem_21b_entries_bounded`).

Under this hypothesis, after `t` squarings the entry at `(i, j)` is the least weight of a walk from
`i` to `j` with at most `2^t` edges: it is the weight of such a walk (`exists_walk_of_entry`) and at
most the weight of every such walk (`entry_le_walkWeight`).  Cutting closed pieces out of a walk
shows that fewer than `n` edges are enough (`exists_short_walk`), and a walk of finite weight with
`k` edges has weight at most `kU` in absolute value (`abs_walkWeight_le`).
-/

public section

namespace ThreeSumApsp

namespace Theorem21



























































































































/-- If the edge weights are at most `U` in absolute value, a walk of finite weight with `k` edges
has weight at most `kU` in absolute value. -/
theorem abs_walkWeight_le {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (U : R) (hwU : EdgeWeightsBoundedBy w U) (i : Fin n)
    (rest : List (Fin n)) (x : R) (hx : walkWeight w i rest = (x : WithTop R)) :
    |x| ≤ rest.length • U := by
  induction rest generalizing i x with
  | nil =>
    obtain rfl : x = 0 := (WithTop.coe_injective (hx : ((0 : R) : WithTop R) = x)).symm
    simp
  | cons j rest ih =>
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.mp hx
    rw [← hab, List.length_cons, succ_nsmul']
    exact (abs_add_le a b).trans (add_le_add (hwU i j a ha.symm) (ih j b hb.symm))

end Theorem21

/-- For **Theorem 21(b)**, repeated squaring: if no closed walk has negative weight, then squaring
the weight matrix `⌈log₂ n⌉` times in the (min,+)-product yields the distance matrix.
(`Nat.clog 2 n` is `⌈log₂ n⌉`.)  Stated for weights in any linearly ordered commutative group, so
that it covers integer and real weights. -/
theorem theorem_21b_repeated_squaring {R : Type} [AddCommGroup R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : ℕ} (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) :
    IsDistanceMatrix w (minPlusSquares w (Nat.clog 2 n)) := by
  intro i j
  constructor
  · obtain ⟨rest, hend, -, hweight⟩ := Theorem21.exists_walk_of_entry w (Nat.clog 2 n) i j
    exact ⟨rest, hend, hweight⟩
  · rintro x ⟨rest, rfl, rfl⟩
    -- A shortest walk needs fewer than `n ≤ 2^⌈log₂ n⌉` edges.
    obtain ⟨rest', hend, hlt, -, hle⟩ := Theorem21.exists_short_walk w hw i rest
    rw [← hend]
    exact (Theorem21.entry_le_walkWeight w hw _ i rest'
      (hlt.le.trans (Nat.le_pow_clog (by norm_num) n))).trans hle

/-- For **Theorem 21(b)**, repeated squaring: a bound on the entries.  If the edge weights have
absolute value at most `U`, every finite entry of every matrix of the repeated squaring has absolute
value at most `nU`; with `U = n^ν` this is `n^{ν+1}`.

NOTE.  A missing edge has the weight `⊤` here, while the (min,+)-product of Theorem 21(b) is on
integer matrices with entries of absolute value at most `U` (`IsMinPlusProduct`).  Nothing is stated
here about replacing `⊤` by a large number. -/
theorem theorem_21b_entries_bounded {R : Type} [AddCommGroup R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : ℕ} (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) (U : R)
    (hU : 0 ≤ U) (hwU : EdgeWeightsBoundedBy w U) (t : ℕ) (i j : Fin n) (x : R)
    (hx : minPlusSquares w t i j = (x : WithTop R)) : |x| ≤ n • U := by
  -- The entry is the weight of a walk with at most `2^t` edges.  Cutting it short gives a walk with
  -- fewer than `n` edges, whose weight is no larger, and no smaller because the entry is a minimum.
  obtain ⟨rest, hend, hlen, hweight⟩ := Theorem21.exists_walk_of_entry w t i j
  obtain ⟨rest', hend', hlt, hlen', hle⟩ := Theorem21.exists_short_walk w hw i rest
  have hge := Theorem21.entry_le_walkWeight w hw t i rest' (hlen'.trans hlen)
  rw [hend', hend, hx] at hge
  have hshort : walkWeight w i rest' = (x : WithTop R) :=
    le_antisymm (hle.trans (hweight.trans hx).le) hge
  exact (Theorem21.abs_walkWeight_le w U hwU i rest' x hshort).trans
    (nsmul_le_nsmul_left hU hlt.le)

end ThreeSumApsp

end
end

section


/-!
# Repeated squaring on lists of integers

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix `⌈log₂ n⌉`
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most `nU`, where `U` bounds the edge weights. The matrices of the repeated
squaring have entries that may be `+∞`, while a solver for the (min,+)-product works on integers.
Here `+∞` is written as the integer `3nU`.

* `squareList n U ADJ W t` is the list, row by row, after `t` rounds.  A round is a (min,+)-product
  of the list with itself, after which every entry above `nU` is set back to `3nU`.
* One round is right (`Encodes.square`): finite entries have absolute value at most `nU`, so a sum
  with an infinite term is at least `2nU`, and a finite sum is the sum of the two codes.
* By induction the list holds the matrix `minPlusSquares` of the repeated squaring, entry
  by entry (`encodes_squareList`), and after `⌈log₂ n⌉` rounds it holds the distances
  (`squareList_distances`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Entries that may be infinite, as integers -/









/-- A code is at least `-B` if `3B` stands for `+∞` and the numbers are bounded by `B`. -/
private theorem neg_le_untopD {B : ℤ} (hB : 0 ≤ B) {d : WithTop ℤ}
    (hd : ∀ x : ℤ, d = (x : WithTop ℤ) → |x| ≤ B) : -B ≤ d.untopD (3 * B) := by
  cases d with
  | top => rw [WithTop.untopD_top]; omega
  | coe x => exact (abs_le.1 (hd x rfl)).1

/-- If a sum of two entries is `+∞`, then the two codes add up to at least `2B`. -/
private theorem two_mul_le_untopD_add_untopD {B : ℤ} (hB : 0 ≤ B) {d d' : WithTop ℤ}
    (hd : ∀ x : ℤ, d = (x : WithTop ℤ) → |x| ≤ B) (hd' : ∀ x : ℤ, d' = (x : WithTop ℤ) → |x| ≤ B)
    (h : d + d' = ⊤) : 2 * B ≤ d.untopD (3 * B) + d'.untopD (3 * B) := by
  have hlow := neg_le_untopD hB hd
  have hlow' := neg_le_untopD hB hd'
  rcases WithTop.add_eq_top.1 h with rfl | rfl
  · rw [WithTop.untopD_top]; omega
  · rw [WithTop.untopD_top]; omega

/-- If a sum of two entries is a number, then the two codes add up to this number. -/
private theorem untopD_add_untopD_of_coe {INF y : ℤ} {d d' : WithTop ℤ}
    (h : d + d' = (y : WithTop ℤ)) : d.untopD INF + d'.untopD INF = y := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := WithTop.add_eq_coe.1 h
  exact hab

/-! ## The lists of the repeated squaring -/














/-- Each list of the repeated squaring has `n²` entries. -/
theorem length_squareList (n U : ℕ) (ADJ W : List ℤ) (t : ℕ) :
    (squareList n U ADJ W t).length = n * n := by
  cases t <;> simp [squareList, weightList, length_minPlusList]

/-- The list of the weights holds the weight matrix of the graph. -/
theorem encodes_weightList (n : ℕ) (INF : ℤ) (ADJ W : List ℤ) :
    Encodes n INF (weightList n INF ADJ W) (weightMatrix (graphOf n ADJ W)) := by
  intro i j
  rw [entry, weightList, List.getD_map_range _ (Nat.mul_add_lt_mul i.isLt j.isLt),
    Nat.mul_add_div_of_lt j.isLt,
    Nat.mul_add_mod_of_lt j.isLt]
  simp only [weightMatrix, Matrix.of_apply, graphOf, Fin.ext_iff]
  split_ifs <;> rfl

/-- **One round.**  If a list holds a matrix `D` whose finite entries are bounded by `B`, with `3B`
for `+∞`, and the finite entries of the (min,+)-product of `D` with itself are bounded by `B` too,
then the (min,+)-product of the list with itself, with every entry above `B` set to `3B`, holds that
product. -/
theorem Encodes.square {n : ℕ} {B : ℤ} (hB : 1 ≤ B) {L : List ℤ}
    {D : Matrix (Fin n) (Fin n) (WithTop ℤ)} (hL : Encodes n (3 * B) L D)
    (hD : ∀ i j (x : ℤ), D i j = (x : WithTop ℤ) → |x| ≤ B)
    (hD' : ∀ i j (x : ℤ), minPlus D D i j = (x : WithTop ℤ) → |x| ≤ B) :
    Encodes n (3 * B) ((minPlusList n L L).map (clip B (3 * B))) (minPlus D D) := by
  intro i j
  have hB0 : 0 ≤ B := by omega
  rw [entry, minPlusList, List.map_map, List.getD_map_range _ (Nat.mul_add_lt_mul i.isLt j.isLt),
    Function.comp_apply, Nat.mul_add_div_of_lt j.isLt, Nat.mul_add_mod_of_lt j.isLt]
  -- The entry `m` of the product of the lists is the smallest sum of two codes, attained at `k₁`.
  obtain ⟨k₁, hk₁, hmin⟩ := exists_minPlusEntry_eq i.pos L L i j
  lift k₁ to Fin n using hk₁
  rw [hL i k₁, hL k₁ j] at hmin
  have hle : ∀ k : Fin n,
      minPlusEntry n L L i j ≤ (D i k).untopD (3 * B) + (D k j).untopD (3 * B) := fun k => by
    rw [← hL i k, ← hL k j]
    exact minPlusEntry_le n L L i j k.isLt
  generalize minPlusEntry n L L i j = m at hmin hle
  -- The entry of the product of the matrices is the smallest sum of two entries, attained at `k₀`.
  have hinf : ∀ k, minPlus D D i j ≤ D i k + D k j := fun k => Finset.inf_le (Finset.mem_univ k)
  obtain ⟨k₀, -, hk₀⟩ : ∃ k₀ ∈ Finset.univ, minPlus D D i j = D i k₀ + D k₀ j :=
    Finset.exists_mem_eq_inf Finset.univ ⟨i, Finset.mem_univ i⟩ fun k => D i k + D k j
  cases hx : minPlus D D i j with
  | top =>
    -- Every sum is `+∞`, so `m ≥ 2B > B`, and `m` is set to `3B`.
    have hbig := two_mul_le_untopD_add_untopD hB0 (hD i k₁) (hD k₁ j) (top_le_iff.1 (hx ▸ hinf k₁))
    rw [WithTop.untopD_top, clip, if_pos (by omega)]
  | coe x =>
    -- The smallest sum is a number `x ≤ B`.  Then `m = x`, and `m` is not changed.
    have hxB := abs_le.1 (hD' i j x hx)
    have hmx : m ≤ x := (hle k₀).trans_eq (untopD_add_untopD_of_coe (hk₀.symm.trans hx))
    have hxm : x ≤ m := by
      cases hy : D i k₁ + D k₁ j with
      | top =>
        -- `x ≤ B ≤ 2B ≤ m`
        have hbig := two_mul_le_untopD_add_untopD hB0 (hD i k₁) (hD k₁ j) hy
        omega
      | coe y =>
        rw [hmin, untopD_add_untopD_of_coe hy]
        exact WithTop.coe_le_coe.1 (hx ▸ hy ▸ hinf k₁)
    rw [WithTop.untopD_coe, clip, if_neg (by omega)]
    omega

/-- The edge weights of the graph read from lists are bounded if the list of the weights is. -/
theorem edgeWeightsBoundedBy_graphOf {n : ℕ} {ADJ W : List ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hW : AbsLe W U) : EdgeWeightsBoundedBy (graphOf n ADJ W) U := by
  intro i j x hx
  rw [graphOf] at hx
  split_ifs at hx
  · obtain rfl := WithTop.coe_injective hx
    exact AbsLe.abs_getD_le hU hW _
  · exact absurd hx WithTop.top_ne_coe

variable {n U : ℕ} {ADJ W : List ℤ}

/-- For Theorem 21(b): the finite entries of the matrices of the repeated squaring have absolute
value at most `nU`. -/
theorem abs_minPlusSquares_le (hW : AbsLe W U) (hc : NoNegativeCycle (graphOf n ADJ W)) (t : ℕ)
    (i j : Fin n) (x : ℤ)
    (hx : minPlusSquares (graphOf n ADJ W) t i j = (x : WithTop ℤ)) : |x| ≤ ((n * U : ℕ) : ℤ) := by
  simpa using theorem_21b_entries_bounded (graphOf n ADJ W) hc (U : ℤ) (by positivity)
    (edgeWeightsBoundedBy_graphOf (by positivity) hW) t i j x hx

/-- **Repeated squaring on lists.**  After `t` rounds the list holds the matrix after `t` squarings
(`minPlusSquares`). -/
theorem encodes_squareList (hn : 1 ≤ n) (hU : 1 ≤ U) (hW : AbsLe W U)
    (hc : NoNegativeCycle (graphOf n ADJ W)) (t : ℕ) :
    Encodes n (3 * (n * U : ℕ)) (squareList n U ADJ W t) (minPlusSquares (graphOf n ADJ W) t) := by
  induction t with
  | zero => exact encodes_weightList _ _ _ _
  | succ t ih =>
    exact Encodes.square (by exact_mod_cast Nat.mul_pos hn hU) ih (abs_minPlusSquares_le hW hc t)
      (abs_minPlusSquares_le hW hc (t + 1))

/-- The entries of the lists of the repeated squaring are bounded by `3nU`. -/
theorem abs_squareList_le (hn : 1 ≤ n) (hU : 1 ≤ U) (hW : AbsLe W U)
    (hc : NoNegativeCycle (graphOf n ADJ W)) (t : ℕ) :
    AbsLe (squareList n U ADJ W t) (3 * (n * U) : ℕ) := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul (length_squareList n U ADJ W t ▸ hq)
  rw [← List.getD_eq_getElem _ 0 hq, ← entry, encodes_squareList hn hU hW hc t ⟨a, ha⟩ ⟨b, hb⟩]
  cases hd : minPlusSquares (graphOf n ADJ W) t ⟨a, ha⟩ ⟨b, hb⟩ with
  | top =>
    rw [WithTop.untopD_top, abs_of_nonneg (by positivity)]
    exact le_of_eq (by push_cast; rfl)
  | coe y =>
    have hy := abs_minPlusSquares_le hW hc t _ _ y hd
    rw [WithTop.untopD_coe]
    omega

/-- **The answer.**  After `⌈log₂ n⌉` rounds the list holds the distances: an entry is `3nU` if and
only if the distance is `+∞`, and it is the distance otherwise. -/
theorem squareList_distances (hn : 1 ≤ n) (hU : 1 ≤ U) (hW : AbsLe W U)
    (hc : NoNegativeCycle (graphOf n ADJ W)) :
    ∃ dist : Fin n → Fin n → WithTop ℤ, IsDistanceMatrix (graphOf n ADJ W) dist ∧ ∀ i j : Fin n,
      (dist i j = ⊤ → entry n (squareList n U ADJ W (Nat.clog 2 n)) i j = 3 * (n * U : ℕ)) ∧
      ∀ z : ℤ, dist i j = (z : WithTop ℤ) →
        entry n (squareList n U ADJ W (Nat.clog 2 n)) i j = z ∧ z ≠ 3 * (n * U : ℕ) := by
  refine ⟨minPlusSquares (graphOf n ADJ W) (Nat.clog 2 n), theorem_21b_repeated_squaring _ hc,
    fun i j => ⟨fun h => ?_, fun z h => ?_⟩⟩
  · rw [encodes_squareList hn hU hW hc _ i j, h, WithTop.untopD_top]
  · rw [encodes_squareList hn hU hW hc _ i j, h, WithTop.untopD_coe]
    have hz := abs_le.1 (abs_minPlusSquares_le hW hc _ i j z h)
    have hpos : 1 ≤ n * U := Nat.mul_pos hn hU
    exact ⟨rfl, by omega⟩

end ThreeSumApsp.Spec

end
end

section


/-!
# APSP by repeated squaring: the three passes over the matrix

For Theorem 21(b).  The host for APSP keeps the current matrix as a list of
`n²` integers, in which a large number `INF` stands for `+∞`.  This file has its three simple
passes, each with its specification (`clip_meets`, `apInit_meets`, `apOut_meets`).

* clip(len, thr, INF, src, dst) copies `len` cells from `src` to `dst` and replaces every number
  above `thr` by `INF`.
* apInit(n, INF, adj, w, A) writes the weight matrix of the graph to `A`: 0 on the diagonal, the
  weight where there is an edge, `INF` elsewhere.
* apOut(len, INF, A, out) writes two cells for each cell of `A`: (0, 0) for `INF`, and (1, x) for
  any other number `x`.

In each proof the memory after j rounds is written down (`wrote`, `zeroedDiag`), one lemma says what
a round does to the state, and the loop rule does the rest.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## clip -/

namespace Clip














end Clip










/-- **clip** writes the clipped list to dst, changes nothing else, and takes at most 23 len + 6
steps. -/
theorem clip_meets {p : ℕ} (hp : P[p]? = some clipBody) {μ : ℕ → ℤ} {src dst : ℕ} {thr INF : ℤ}
    {L : List ℤ} (hL : Seg μ src L) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src + L.length ≤ lim.space) (hdst : dst + L.length ≤ lim.space)
    (hsep : src + L.length ≤ dst ∨ dst + L.length ≤ src) :
    Meets lim P p d [L.length, thr, INF, src, dst] μ (23 * L.length + 6) fun _ μ' =>
      Seg μ' dst (L.map (clip thr INF)) ∧ SameOutside μ μ' dst L.length := by
  refine .of_body hp ?_
  refine Ends.forFrame (fun j μ' => μ' = wrote μ dst (fun i => clip thr INF (L.getD i 0)) j)
    L.length wrote_zero.symm ?round ?done (hT := by simp; omega)
  case round =>
    intro j μ' hj hμ
    have hread : μ' (src + j) = L.getD j 0 :=
      hμ ▸ (wrote_rest (by omega)).trans (hL.getD hj 0)
    have hnext : Function.update μ' (dst + j) (clip thr INF (L.getD j 0)) = _ := hμ ▸ wrote_succ
    -- from here on x = src[j]
    generalize L.getD j 0 = x at hread hnext
    -- if Thresh < mem[Src + Idx]
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by (((try have := Light.Std.space_le (by assumption)));
                                                            ((try have := Light.Std.const_le (by assumption)));
                                                            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    · have hc' : thr < x := by simpa [hread] using hc
      rw [clip, if_pos hc'] at hnext
      -- mem[Dst + Idx] := Big
      focus
        ((((first
                | refine Light.Ends.seqSelf ?_
                | refine Light.Ends.skipLast ?_));
            (repeat
                with_unfolding_none
                  first
                  | refine Light.Ends.seqAssoc ?_
                  | refine Light.Ends.skipThen ?_)));
        (refine Light.Ends.storeToThen (dst + j) INF ?_ ?_ ?_);
        (on_goal -1 =>
            first
            |
              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                (first
                  | omega
                  | ((ring_nf); (omega))))
            | omega
            |
              (simp [] <;>
                  first
                  | omega
                  | ((ring_nf); (omega))));
        (on_goal -1 =>
            (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
        (try with_unfolding_none refine Light.Ends.skip ?_)
      exact ⟨rfl, hnext⟩
    · have hc' : ¬ thr < x := by simpa [hread] using hc
      rw [clip, if_neg hc'] at hnext
      -- mem[Dst + Idx] := mem[Src + Idx]
      focus
        ((((first
                | refine Light.Ends.seqSelf ?_
                | refine Light.Ends.skipLast ?_));
            (repeat
                with_unfolding_none
                  first
                  | refine Light.Ends.seqAssoc ?_
                  | refine Light.Ends.skipThen ?_)));
        (refine Light.Ends.storeToThen (dst + j) x ?_ ?_ ?_);
        (on_goal -1 =>
            first
            |
              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hread]);
                (first
                  | omega
                  | ((ring_nf); (omega))))
            | omega
            |
              (simp [hread] <;>
                  first
                  | omega
                  | ((ring_nf); (omega))));
        (on_goal -1 =>
            (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul, hread] <;> omega)));
        (try with_unfolding_none refine Light.Ends.skip ?_)
      exact ⟨rfl, hnext⟩
  case done =>
    rintro _ rfl
    dsimp only
    exact ⟨seg_wrote_map _ L, sameOutside_wrote le_rfl⟩

/-! ## apInit -/

namespace ApInit


















end ApInit




























private theorem zeroedDiag_zero {μ : ℕ → ℤ} {A n : ℕ} : zeroedDiag μ A n 0 = μ := by
  funext a
  simp [zeroedDiag]

/-- What round j of the second pass writes. -/
private theorem zeroedDiag_succ {μ : ℕ → ℤ} {A n : ℕ} (j : ℕ) :
    Function.update (zeroedDiag μ A n j) (A + j * (n + 1)) 0 = zeroedDiag μ A n (j + 1) := by
  funext a
  simp only [zeroedDiag, Nat.exists_lt_succ_right, Function.update_apply]
  by_cases h : a = A + j * (n + 1) <;> simp [h]

/-- After both passes the weight matrix stands at A. -/
private theorem seg_zeroedDiag_wrote {μ : ℕ → ℤ} {A n : ℕ} {INF : ℤ} {ADJ W : List ℤ} :
    Seg (zeroedDiag (wrote μ A (apInitCell INF ADJ W) (n * n)) A n n) A
      (weightList n INF ADJ W) := by
  intro q hq
  have hq' : q < n * n := by simpa [weightList] using hq
  have hdiag : (∃ i < n, A + q = A + i * (n + 1)) ↔ q / n = q % n :=
    ⟨fun ⟨i, hi, h⟩ => by
      obtain ⟨h1, h2⟩ := (Nat.eq_mul_succ_iff hi).1 (Nat.add_left_cancel h)
      rw [h1, h2],
    fun h => ⟨q % n, Nat.mod_lt_of_lt_mul hq', congrArg (A + ·)
      ((Nat.eq_mul_succ_iff (Nat.mod_lt_of_lt_mul hq')).2 ⟨h, rfl⟩)⟩⟩
  simp only [zeroedDiag, hdiag, wrote_done hq', weightList, List.getElem_map, List.getElem_range,
    apInitCell]

/-- Both passes change the n² cells of A only. -/
private theorem sameOutside_zeroedDiag {μ μ' : ℕ → ℤ} {A n j : ℕ} (h : SameOutside μ μ' A (n * n))
    (hj : j ≤ n) : SameOutside μ (zeroedDiag μ' A n j) A (n * n) := by
  intro a ha
  have hno : ¬ ∃ i < j, a = A + i * (n + 1) := by
    rintro ⟨i, hi, rfl⟩
    have := Nat.mul_add_lt_mul (show i < n by omega) (show i < n by omega)
    rw [Nat.mul_succ] at ha
    simp only [Outside] at ha
    omega
  rw [zeroedDiag, if_neg hno]
  exact h a ha






/-- **One round of the first pass of apInit**, for the cells adj[j] = x and w[j] = y: the weight y
where there is an edge, and INF where there is none. -/
private theorem apInitFill_spec {μ : ℕ → ℤ} {adj w A j : ℕ} {n INF nn x y : ℤ}
    (hx : μ (adj + j) = x) (hy : μ (w + j) = y) (hw : (lim.space : ℤ) ≤ lim.word)
    (hplace : adj + j < lim.space ∧ w + j < lim.space ∧ A + j < lim.space) :
    Ends lim P d apInitFill ⟨frame [n, INF, adj, w, A, j, nn], μ⟩ apInitFill.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, adj, w, A, j, nn],
        Function.update μ (A + j) (if x = 1 then y else INF)⟩ := by
  unfold apInitFill
  -- if mem[AdjAt + Idx] = 1
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by (((try have := Light.Std.space_le (by assumption)));
                                                          ((try have := Light.Std.const_le (by assumption)));
                                                          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
  · have hc' : x = 1 := by simpa [hx] using hc
    rw [if_pos hc']
    -- mem[Mat + Idx] := mem[WtsAt + Idx]
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (A + j) y ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hy]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hy] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hy] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    rfl
  · have hc' : x ≠ 1 := by simpa [hx] using hc
    rw [if_neg hc']
    -- mem[Mat + Idx] := Big
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (A + j) INF ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    rfl

/-- **One round of the second pass of apInit**, for the address o of the diagonal cell.  The next
address o + n + 1 is computed also in the last round, so it has to fit. -/
private theorem apInitDiag_spec {μ : ℕ → ℤ} {n o : ℕ} {INF adj w A j : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (ho : o + n + 1 ≤ lim.space) :
    Ends lim P d apInitDiag ⟨frame [n, INF, adj, w, A, j, o], μ⟩ apInitDiag.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, adj, w, A, j, (o + (n + 1) : ℕ)], Function.update μ o 0⟩ := by
  unfold apInitDiag
  -- mem[Diag] := 0 ; Diag := Diag + Verts + 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen o 0 ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (o + (n + 1) : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  rfl

/-- **apInit** writes the weight matrix to A, changes nothing else, and takes at most
23 n² + 17 n + 18 steps.  Only n² cells are written; the space 2 n² is asked for because after the
last round of the second pass the local Diag holds A + n (n + 1), which has to fit. -/
theorem apInit_meets {p : ℕ} (hp : P[p]? = some apInitBody) {μ : ℕ → ℤ} {n adj w A : ℕ} {INF : ℤ}
    {ADJ W : List ℤ} (hn : 1 ≤ n) (lenADJ : ADJ.length = n * n) (lenW : W.length = n * n)
    (segADJ : Seg μ adj ADJ) (segW : Seg μ w W) (hw : (lim.space : ℤ) ≤ lim.word)
    (hadj : adj + n * n ≤ lim.space) (hwt : w + n * n ≤ lim.space)
    (hA : A + 2 * (n * n) ≤ lim.space) (sepADJ : adj + n * n ≤ A ∨ A + n * n ≤ adj)
    (sepW : w + n * n ≤ A ∨ A + n * n ≤ w) :
    Meets lim P p d [n, INF, adj, w, A] μ (23 * (n * n) + 17 * n + 18) fun _ μ' =>
      Seg μ' A (weightList n INF ADJ W) ∧ SameOutside μ μ' A (n * n) := by
  refine .of_body hp ?_
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  have hword : (n : ℤ) * n ≤ lim.word := by exact_mod_cast (show ((n * n : ℕ) : ℤ) ≤ _ by omega)
  have hpos : 0 ≤ (n : ℤ) * n := by positivity
  unfold apInitBody
  -- Cells := Verts * Verts
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (n * n : ℕ)
            -- for Idx < Cells: the first pass
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- for Idx < Cells: the first pass
  refine Ends.next _ (Ends.forFrame (fun j μ' => μ' = wrote μ A (apInitCell INF ADJ W) j)
    (n * n) wrote_zero.symm ?round ?done (hT := le_rfl)) (by simp [apInitFill]; omega)
  case round =>
    rintro j _ hj rfl
    -- the cells adj[j] and w[j] are as at the start
    have hadjCell : wrote μ A (apInitCell INF ADJ W) j (adj + j) = ADJ.getD j 0 :=
      (wrote_rest (by omega)).trans (segADJ.getD (lenADJ ▸ hj) 0)
    have hwtCell : wrote μ A (apInitCell INF ADJ W) j (w + j) = W.getD j 0 :=
      (wrote_rest (by omega)).trans (segW.getD (lenW ▸ hj) 0)
    refine (apInitFill_spec hadjCell hwtCell hw (by omega)).mono le_rfl ?_
    rintro _ rfl
    exact ⟨rfl, wrote_succ⟩
  case done =>
    rintro _ rfl
    -- Diag := Mat
    refine Ends.setToThen A ?_ (hT := by simp [apInitFill]; omega)
    -- for Idx < Verts: the second pass
    refine Ends.for (ApInitInv (wrote μ A (apInitCell INF ADJ W) (n * n)) n adj w A INF) n
      apInitDiag.blockCost ?start ?round ?done ?bound (by omega)
      (by simp [apInitFill, apInitDiag]; omega)
    case start =>
      rw [ApInitInv, zeroedDiag_zero, Nat.zero_mul, Nat.add_zero]
      exact congrArg (State.mk · _) (update_frame_setLocal _ _ _)
    case round =>
      rintro j _ hj - rfl
      have hrow := Nat.mul_add_le_mul hj (le_refl (n + 1))
      rw [Nat.mul_succ n n] at hrow
      refine (apInitDiag_spec hw (by omega)).mono le_rfl ?_
      rintro _ rfl
      exact ⟨rfl, by rw [ApInitInv, update_frame_setLocal, Nat.cast_succ, zeroedDiag_succ,
        Nat.succ_mul, Nat.add_assoc]; rfl⟩
    case done =>
      rintro _ - rfl
      exact ⟨seg_zeroedDiag_wrote, sameOutside_zeroedDiag (sameOutside_wrote le_rfl) le_rfl⟩
    case bound =>
      rintro j _ - - rfl
      exact ⟨trivial, rfl⟩

/-! ## apOut -/

namespace ApOut














end ApOut






















/-- What round q writes. -/
private theorem wrote_apOutCell_succ {μ : ℕ → ℤ} {out : ℕ} {INF : ℤ} {L : List ℤ} (q : ℕ) :
    Function.update (Function.update (wrote μ out (apOutCell INF L) (2 * q)) (out + 2 * q)
      (if L.getD q 0 = INF then 0 else 1)) (out + 2 * q + 1)
      (if L.getD q 0 = INF then 0 else L.getD q 0) =
        wrote μ out (apOutCell INF L) (2 * (q + 1)) := by
  have heven : apOutCell INF L (2 * q) = if L.getD q 0 = INF then 0 else 1 := by
    simp only [apOutCell, Nat.mul_div_cancel_left q Nat.two_pos, Nat.mul_mod_right, if_true]
  have hodd : apOutCell INF L (2 * q + 1) = if L.getD q 0 = INF then 0 else L.getD q 0 := by
    simp only [apOutCell, show (2 * q + 1) / 2 = q by omega, show (2 * q + 1) % 2 = 1 by omega,
      one_ne_zero, if_false]
  rw [← heven, wrote_succ, Nat.add_assoc, ← hodd, wrote_succ]
  rfl





/-- **The two stores of a round of apOut**, for the cell A[j] = x and the address o of the output.
-/
private theorem apOutWrite_spec {μ : ℕ → ℤ} {A out o j : ℕ} {n INF x : ℤ} (hread : μ (A + j) = x)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hplace : A + j < lim.space ∧ o + 1 < lim.space ∧ A + j ≠ o) :
    Ends lim P d apOutWrite ⟨frame [n, INF, A, out, j, o], μ⟩ apOutWrite.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, A, out, j, o], Function.update (Function.update μ o
        (if x = INF then 0 else 1)) (o + 1) (if x = INF then 0 else x)⟩ := by
  unfold apOutWrite
  -- if mem[Mat + Idx] = Big
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by (((try have := Light.Std.space_le (by assumption)));
                                                          ((try have := Light.Std.const_le (by assumption)));
                                                          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
  · have hc' : x = INF := by simpa [hread] using hc
    rw [if_pos hc', if_pos hc']
    -- mem[Pos] := 0 ; mem[Pos + 1] := 0
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen o 0 ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (o + 1) 0 ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    rfl
  · have hc' : x ≠ INF := by simpa [hread] using hc
    rw [if_neg hc', if_neg hc']
    -- mem[Pos] := 1 ; mem[Pos + 1] := mem[Mat + Idx]
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen o 1 ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (o + 1) x ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  Function.update_of_ne hplace.2.2, hread]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [Function.update_of_ne hplace.2.2, hread] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul,
                  Function.update_of_ne hplace.2.2, hread] <;>
                omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    rfl

/-- **One round of apOut** writes the pair for the cell A[j] and moves Pos on by two. -/
private theorem apOutRound_spec {μ : ℕ → ℤ} {A out : ℕ} {INF : ℤ} {L : List ℤ} (hL : Seg μ A L)
    (hw : (lim.space : ℤ) ≤ lim.word) (hA : A + L.length ≤ lim.space)
    (hout : out + 2 * L.length ≤ lim.space) (hsep : A + L.length ≤ out ∨ out + 2 * L.length ≤ A)
    {j : ℕ} (hj : j < L.length) :
    Ends lim P d apOutRound
      ⟨frame [L.length, INF, A, out, j, (out + 2 * j : ℕ)], wrote μ out (apOutCell INF L) (2 * j)⟩
      apOutRound.blockCost fun σ' =>
        σ' = ⟨frame [L.length, INF, A, out, j, (out + 2 * (j + 1) : ℕ)],
          wrote μ out (apOutCell INF L) (2 * (j + 1))⟩ := by
  have hread : wrote μ out (apOutCell INF L) (2 * j) (A + j) = L.getD j 0 :=
    (wrote_rest (by omega)).trans (hL.getD hj 0)
  rw [← wrote_apOutCell_succ]
  refine Ends.next _ ((apOutWrite_spec hread hw (by omega)).mono le_rfl ?_)
    (by simp [apOutRound])
  rintro _ rfl
  -- Pos := Pos + 2
  exact Ends.setTo (out + 2 * (j + 1) : ℕ) rfl (by (((try have := Light.Std.space_le (by assumption)));
                                                       ((try have := Light.Std.const_le (by assumption)));
                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (by simp [apOutRound])







/-- **apOut** writes the pairs to out, changes nothing else, and takes at most 30 len + 8 steps. -/
theorem apOut_meets {p : ℕ} (hp : P[p]? = some apOutBody) {μ : ℕ → ℤ} {A out : ℕ} {INF : ℤ}
    {L : List ℤ} (hL : Seg μ A L) (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : A + L.length ≤ lim.space) (hout : out + 2 * L.length ≤ lim.space)
    (hsep : A + L.length ≤ out ∨ out + 2 * L.length ≤ A) :
    Meets lim P p d [L.length, INF, A, out] μ (30 * L.length + 8) fun _ μ' =>
      PairsAt μ' out INF L ∧ SameOutside μ μ' out (2 * L.length) := by
  refine .of_body hp ?_
  unfold apOutBody
  -- Pos := Out
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen out ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  refine Ends.for (ApOutInv μ A out INF L) L.length apOutRound.blockCost ?start ?round ?done ?bound
    (by omega) (by simp [apOutRound, apOutWrite]; omega)
  case start =>
    rw [ApOutInv, wrote_zero]
    exact congrArg (State.mk · μ) (update_frame_setLocal _ _ _)
  case round =>
    rintro j _ hj - rfl
    refine (apOutRound_spec hL hw hA hout hsep hj).mono le_rfl ?_
    rintro _ rfl
    exact ⟨rfl, by rw [ApOutInv, update_frame_setLocal, Nat.cast_succ]; rfl⟩
  case done =>
    rintro _ - rfl
    refine ⟨fun i hi => ?_, sameOutside_wrote le_rfl⟩
    change (_ → wrote μ out (apOutCell INF L) (2 * L.length) (out + 2 * i) = 0) ∧
      (_ → wrote μ out (apOutCell INF L) (2 * L.length) (out + 2 * i) = 1 ∧
        wrote μ out (apOutCell INF L) (2 * L.length) (out + 2 * i + 1) = L[i])
    rw [wrote_done (by omega), Nat.add_assoc, wrote_done (by omega), apOutCell, apOutCell,
      show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega,
      List.getD_eq_getElem _ _ hi]
    exact ⟨fun h => if_pos h, fun h => ⟨by simp [h], by simp [h]⟩⟩
  case bound =>
    rintro j _ - - rfl
    exact ⟨trivial, rfl⟩

end Light.Sec3

end
end

section


/-!
# APSP from the (min,+)-product

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix ⌈log₂ n⌉
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most nU, where U bounds the edge weights.  The host below does this over an
arbitrary solver of the (min,+)-product.

ap(n, U, adj, w, out, fr) keeps the current matrix in the `n²` cells from `fr`, with `3nU` for `+∞`;
the product is written to the next `n²` cells, and the solver gets the free pointer `fr + 2n²`.
After each product the entries above `nU` are set back to `3nU` while the matrix is copied back.
The rounds are counted by doubling a number that starts at 1, as long as it is below `n`: these are
`⌈log₂ n⌉` rounds.

The proof follows the text: one round squares the matrix (`ApspHost.round_spec`), the last call
writes the answer (`ApspHost.out_spec`, `ApspHost.answer_correct`), and `ap_spec` puts the parts
together.  The result is `isHost_ap : IsHost mpTask apTask apTime apNeed`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace ApspHost




























end ApspHost

































namespace ApspHost
























variable {P₀ R₀ : Program} {pMP pInit pClip pOut : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {lim : Limits} {d : ℕ} {x : GraphInst} {μ : ℕ → ℤ} {fr : ℕ}

/-- The arithmetic facts of the hypotheses as one conjunction: what the limits allow and what the
instance satisfies. -/
private theorem Ctx.places (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) :
    ((lim.space : ℤ) ≤ lim.word ∧ 3 * ((x.n : ℤ) * x.U) ≤ lim.word ∧
      ((r x.n (3 * (x.n * x.U))).word : ℤ) ≤ lim.word ∧
      fr + (2 * (x.n * x.n) + (r x.n (3 * (x.n * x.U))).cells) ≤ lim.space ∧
      d + ((r x.n (3 * (x.n * x.U))).depth + 1) ≤ lim.depth) ∧
      x.n ≤ x.n * x.n ∧ 1 ≤ x.n * x.U ∧ x.adj + x.n * x.n ≤ fr ∧ x.w + x.n * x.n ≤ fr ∧
      x.out + 2 * (x.n * x.n) ≤ fr :=
  ⟨⟨C.ok.space, by exact_mod_cast le_trans (Nat.cast_le.2 (le_max_right _ _)) C.ok.word,
    le_trans (by exact_mod_cast le_max_left _ _) C.ok.word, C.ok.cells, C.ok.depth⟩,
    Nat.le_mul_of_pos_left _ C.pre.n_pos, Nat.mul_pos C.pre.n_pos C.pre.U_pos, C.pre.belowADJ,
    C.pre.belowW, C.pre.belowOut⟩

/-- The pairs that apOut writes for the matrix after ⌈log₂ n⌉ squarings are the answer. -/
private theorem answer_correct (hpre : x.Pre μ fr) {μ' : ℕ → ℤ}
    (hans : PairsAt μ' x.out (3 * (x.n * x.U : ℕ))
      (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n))) :
    ∃ dist : Fin x.n → Fin x.n → WithTop ℤ, IsDistanceMatrix (graphOf x.n x.ADJ x.W) dist ∧
      ∀ i j : Fin x.n, (dist i j = ⊤ → μ' (x.out + 2 * (i.val * x.n + j.val)) = 0) ∧
        ∀ z : ℤ, dist i j = (z : WithTop ℤ) → μ' (x.out + 2 * (i.val * x.n + j.val)) = 1 ∧
          μ' (x.out + 2 * (i.val * x.n + j.val) + 1) = z := by
  obtain ⟨dist, hdist, hentries⟩ :=
    squareList_distances hpre.n_pos hpre.U_pos hpre.leW hpre.noNegativeCycle
  refine ⟨dist, hdist, fun i j => ?_⟩
  have hq : i.val * x.n + j.val < (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n)).length := by
    rw [length_squareList]
    exact Nat.mul_add_lt_mul i.isLt j.isLt
  obtain ⟨htop, hfin⟩ := hentries i j
  rw [entry, List.getD_eq_getElem _ _ hq] at htop hfin
  obtain ⟨hzero, hone⟩ := hans _ hq
  refine ⟨fun h => hzero (htop h), fun z hz => ?_⟩
  obtain ⟨hval, hne⟩ := hfin z hz
  exact hval ▸ hone (hval ▸ hne)

/-- **One round of the host** squares the matrix at the free pointer: a (min,+)-product, the
clipping of the large entries, and the doubling of Power. -/
private theorem round_spec (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) {t : ℕ}
    (ht : 2 ^ t < x.n) {σ : State} (hσ : Inv x μ fr t σ) :
    Ends lim (P₀ ++ R₀) d (apRound pMP pClip) σ (T x.n (3 * (x.n * x.U)) + 23 * (x.n * x.n) + 25)
      (Inv x μ fr (t + 1)) := by
  obtain ⟨res, μ', rfl, hseg, hkept⟩ := hσ
  have hplaces := C.places
  have hw := C.ok.space
  set L := squareList x.n x.U x.ADJ x.W t
  have hlen : L.length = x.n * x.n := length_squareList _ _ _ _ _
  have hlenP : (minPlusList x.n L L).length = x.n * x.n := length_minPlusList _ _ _
  have hle : AbsLe L ((3 * (x.n * x.U) : ℕ) : ℤ) :=
    abs_squareList_le C.pre.n_pos C.pre.U_pos C.pre.leW C.pre.noNegativeCycle t
  unfold apRound
  -- Res := pMP(Verts, Big, Free, Free, ProdAt, SolverFree)
  refine Ends.callToThen (C.solver.meets R₀
    (⟨x.n, 3 * (x.n * x.U), fr, fr, fr + x.n * x.n, L, L⟩ : MatInst) (fr + 2 * (x.n * x.n))
    ⟨C.pre.n_pos, by simp only; omega, hlen, hlen, hseg, hseg, hle, hle, by simp only; omega,
      by simp only; omega, by simp only; omega, Or.inl le_rfl, Or.inl le_rfl⟩
    { word := by simp only [mpTask]; omega
      cells := by simp only [mpTask]; omega
      space := hw
      depth := by simp only [mpTask]; omega }) ?_ (by simp [mpTask]) (by omega)
        (by simp [mpTask]; omega)
  rintro r₁ μ₁ ⟨hprod, hkept₁⟩
  simp only at hprod hkept₁
  -- Res := pClip(Cells, Thresh, Big, ProdAt, Free)
  refine Ends.callToThen (clip_meets C.clip (thr := (x.n * x.U : ℕ)) (INF := 3 * (x.n * x.U : ℕ))
    (dst := fr) hprod hw (by omega) (by omega) (Or.inr (by omega))) ?_ (by simp [hlenP])
    (by omega) (by simp [mpTask, hlenP]; omega)
  rintro r₂ μ₂ ⟨hseg₂, hsame₂⟩
  rw [hlenP] at hsame₂
  -- Power := Power + Power
  refine Ends.setTo (2 ^ (t + 1) : ℕ) ⟨r₂, μ₂, rfl, hseg₂, fun a ha => ?_⟩ ?_
    (by simp [mpTask, hlenP]; omega)
  · ((try refine Light.SameOn.cell ?_); (intro apspMacro_96460_0 apspMacro_96460_1);
       (first
         |
           ((((repeat
                     (((with_reducible
                             rename Light.SameOn _ _ _ => apspMacro_96460_2));
                       ((try
                             have :=
                               apspMacro_96460_2 apspMacro_96460_0 (by omega)));
                       (revert apspMacro_96460_2)));
                 (intros);
                 (try simp only [Function.update_apply, Light.wrote] at *)));
             (omega))
         |
           ((simp [] at apspMacro_96460_1);
             (((repeat
                     (((with_reducible
                             rename Light.SameOn _ _ _ => apspMacro_96460_3));
                       ((try
                             have :=
                               apspMacro_96460_3 apspMacro_96460_0 (by omega)));
                       (revert apspMacro_96460_3)));
                 (intros);
                 (try simp only [Function.update_apply, Light.wrote] at *)));
             (omega))
         |
           ((((repeat
                     (((with_reducible
                             rename Light.SameOn _ _ _ => apspMacro_96460_4));
                       ((try
                             have :=
                               apspMacro_96460_4 apspMacro_96460_0 (by omega)));
                       (revert apspMacro_96460_4)));
                 (intros);
                 (try simp only [Function.update_apply, Light.wrote] at *)));
             (fail
                 "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                           SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                           its condition K x does not follow from the hypotheses."))))
  · have hpow : (2 : ℤ) ^ t < x.n := by exact_mod_cast ht
    have hpos : (0 : ℤ) ≤ 2 ^ t := by positivity
    simp [abs_le, pow_succ]
    omega

/-- **The end of the host**: the answer is written. -/
private theorem out_spec (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) {σ : State}
    (hσ : Inv x μ fr (Nat.clog 2 x.n) σ) :
    Ends lim (P₀ ++ R₀) d (.call pOut [v Cells, v Big, v Free, v Out] Res) σ (30 * (x.n * x.n) + 14)
      fun σ' => apTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  obtain ⟨res, μ', rfl, hseg, hkept⟩ := hσ
  have hplaces := C.places
  have hw := C.ok.space
  have hlen : (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n)).length = x.n * x.n :=
    length_squareList _ _ _ _ _
  -- Res := pOut(Cells, Big, Free, Out)
  refine Ends.callTo (apOut_meets C.out (INF := 3 * (x.n * x.U : ℕ)) (out := x.out) hseg hw
    (by omega) (by omega) (Or.inr (by omega))) ?_ (by simp [hlen]) (hT := by rw [hlen]; first
                                                                                        |
                                                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                            (first
                                                                                              | omega
                                                                                              | ((ring_nf); (omega))))
                                                                                        | omega
                                                                                        |
                                                                                          (simp [] <;>
                                                                                              first
                                                                                              | omega
                                                                                              | ((ring_nf); (omega))))
  rintro r₂ μ₂ ⟨hans, hsame₂⟩
  rw [hlen] at hsame₂
  exact ⟨answer_correct C.pre hans, fun a ⟨ha, hout⟩ => (hsame₂ a hout).trans (hkept a ha)⟩

end ApspHost

open ApspHost in
/-- **The host is correct**, in every program that begins with the solver's program and has the
three passes. -/
theorem ap_spec {P₀ R₀ : Program} {pMP pInit pClip pOut : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    {lim : Limits} {d : ℕ} {x : GraphInst} {μ : ℕ → ℤ} {fr : ℕ}
    (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) :
    Ends lim (P₀ ++ R₀) d (apBody pMP pInit pClip pOut) ⟨frame (apTask.args x ++ [(fr : ℤ)]), μ⟩
      (apTime T x.n x.U) fun σ' => apTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hplaces := C.places
  have hw := C.ok.space
  have hpre := C.pre
  have hsquare : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
  have hthresh : (0 : ℤ) ≤ (x.n : ℤ) * x.U := by positivity
  unfold apBody apTime
  change Ends _ _ _ _ ⟨frame [(x.n : ℤ), x.U, x.adj, x.w, x.out, fr], μ⟩ _ _
  -- Cells := Verts * Verts ; Thresh := Verts * Bound ; Big := 3 * Thresh
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (x.n * x.n : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (x.n * x.U : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (3 * (x.n * x.U : ℕ))
            -- ProdAt := Free + Cells ; SolverFree := ProdAt + Cells
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- ProdAt := Free + Cells ; SolverFree := ProdAt + Cells
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (fr + x.n * x.n : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (fr + 2 * (x.n * x.n) : ℕ)
            -- Res := pInit(Verts, Big, AdjAt, WtsAt, Free)
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- Res := pInit(Verts, Big, AdjAt, WtsAt, Free)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (first
      |
        refine
          Light.Ends.callToThen
            ((apInit_meets C.init (INF := 3 * (x.n * x.U : ℕ)) (A := fr)
                hpre.n_pos hpre.lenADJ hpre.lenW hpre.segADJ hpre.segW hw
                (by omega) (by omega) (by omega) (Or.inl hpre.belowADJ)
                (Or.inl hpre.belowW))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (apInit_meets C.init (INF := 3 * (x.n * x.U : ℕ)) (A := fr) hpre.n_pos
              hpre.lenADJ hpre.lenW hpre.segADJ hpre.segW hw (by omega) (by omega)
              (by omega) (Or.inl hpre.belowADJ) (Or.inl hpre.belowW))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro r₁ μ₁
              ⟨hseg₁, hsame₁⟩
                  -- Power := 1
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- Power := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (2 ^ 0 : ℕ)
            -- while Power < Verts: the rounds
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while Power < Verts: the rounds
  refine Ends.next _ (Ends.whileConst (Inv x μ fr) (Nat.clog 2 x.n)
    (T x.n (3 * (x.n * x.U)) + 23 * (x.n * x.n) + 25)
    ⟨r₁, μ₁, rfl, hseg₁, fun a ha => hsame₁ a (Or.inl ha)⟩ ?round ?done le_rfl)
  case round =>
    rintro t σ ht hσ
    have hpow : 2 ^ t < x.n := Nat.pow_lt_of_lt_clog ht
    refine ⟨?_, ?_, round_spec C hpow hσ⟩ <;> obtain ⟨res, μ', rfl, -, -⟩ := hσ
    · exact ⟨trivial, trivial⟩
    · simpa using (by exact_mod_cast hpow : ((2 : ℤ) ^ t < x.n))
  case done =>
    intro σ hσ
    have hpow : x.n ≤ 2 ^ Nat.clog 2 x.n := Nat.le_pow_clog (by norm_num) x.n
    refine ⟨?_, ?_, (out_spec C hσ).mono (by first
                                                |
                                                  ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                    (first
                                                      | omega
                                                      | ((ring_nf); (omega))))
                                                | omega
                                                |
                                                  (simp [] <;>
                                                      first
                                                      | omega
                                                      | ((ring_nf); (omega)))) fun _ h => h⟩ <;>
      obtain ⟨res, μ', rfl, -, -⟩ := hσ
    · exact ⟨trivial, trivial⟩
    · simpa using (by exact_mod_cast hpow : ((x.n : ℤ) ≤ 2 ^ Nat.clog 2 x.n))

/-- The need of the host is polynomially bounded if the need of the solver is. -/
theorem polyNeed_apNeed {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (apNeed r) := by
  unfold apNeed
  (refine Light.PolyBounded.polyNeed ?_ ?_ ?_ <;> dsimp only <;>
      first
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply hr.word
                  | apply hr.cells
                  | apply hr.depth
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div);
          (·
              first
              | decide
              | exact isEmptyElim))
      |
        ((fail_if_success
              (fail_if_success
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (on_goal 1 =>
                        ((repeat'
                              with_reducible
                                first
                                | exact ThreeSumApsp.Scale.SoftO.const _
                                | apply Light.PolyBounded.fst
                                | apply Light.PolyBounded.snd
                                | apply ThreeSumApsp.Scale.SoftO.log
                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                | apply hr.word
                                | apply hr.cells
                                | apply hr.depth
                                | apply ThreeSumApsp.Scale.SoftO.add
                                | apply ThreeSumApsp.Scale.SoftO.mul
                                | apply ThreeSumApsp.Scale.SoftO.pow
                                | apply ThreeSumApsp.Scale.SoftO.max
                                | apply ThreeSumApsp.Scale.SoftO.sub
                                | apply ThreeSumApsp.Scale.SoftO.div);
                          (done))))));
          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
          (all_goals
              try
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (·
                      repeat'
                        with_reducible
                          first
                          | exact ThreeSumApsp.Scale.SoftO.const _
                          | apply Light.PolyBounded.fst
                          | apply Light.PolyBounded.snd
                          | apply ThreeSumApsp.Scale.SoftO.log
                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                          | apply hr.word
                          | apply hr.cells
                          | apply hr.depth
                          | apply ThreeSumApsp.Scale.SoftO.add
                          | apply ThreeSumApsp.Scale.SoftO.mul
                          | apply ThreeSumApsp.Scale.SoftO.pow
                          | apply ThreeSumApsp.Scale.SoftO.max
                          | apply ThreeSumApsp.Scale.SoftO.sub
                          | apply ThreeSumApsp.Scale.SoftO.div);
                  (· decide))))
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply hr.word
                  | apply hr.cells
                  | apply hr.depth
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)))

/-- **APSP from the (min,+)-product**, as a host. -/
theorem isHost_ap : IsHost mpTask apTask apTime apNeed := by
  refine ⟨fun P p T r hs => ?_, fun r hr => polyNeed_apNeed hr⟩
  refine ⟨[apInitBody, clipBody, apOutBody, apBody p P.length (P.length + 1) (P.length + 2)],
    P.length + 3, apBody p P.length (P.length + 1) (P.length + 2), by simp,
    fun R lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact ap_spec ⟨hs, by simp, by simp, by simp, hpre, hok⟩

end Light.Sec3

end
end

section


/-!
# APSP from the (min,+)-product: the claim

The running time of the host (`apTime`, `isHost_ap`) in the form of the claim
`ApspFromMinPlus`: `⌈log₂ n⌉ + 1` times the sum of the time of a (min,+)-product of
matrices whose entries are bounded by `3nu` and of `O(n² (1 + log(nu)))` (for Theorem 21(b)).
-/

public section

namespace Light.Sec3

open ThreeSumApsp

/-- APSP from the (min,+)-product, for programs of the light language. -/
theorem claim_apspFromMinPlus_sourceProof : Claim.ApspFromMinPlus lightModel := by
  refine ⟨3, 135, by norm_num, fun T hT => isHost_ap.solvedIn hT fun Tn hTn n U u hn hU hu => ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hτ : (Tn n (3 * (n * U)) : ℝ) ≤ T n (3 * ((n : ℝ) * u)) := by
    refine hTn n (3 * (n * U)) _ hn (by have := Nat.mul_pos hn hU; omega) ?_
    push_cast
    have : (n : ℝ) * U ≤ n * u := mul_le_mul_of_nonneg_left hu (by positivity)
    linarith
  have hlog : 0 ≤ logU (3 * ((n : ℝ) * u)) :=
    Real.log_nonneg (le_trans (by norm_num) (le_max_right _ _))
  have hτ0 : 0 ≤ T n (3 * ((n : ℝ) * u)) := le_trans (by positivity) hτ
  have hc0 : (0 : ℝ) ≤ (Nat.clog 2 n : ℝ) := by positivity
  have hns : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hs1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hsℓ : 0 ≤ (n : ℝ) ^ 2 * logU (3 * ((n : ℝ) * u)) := by positivity
  simp only [apTime]
  push_cast
  rw [← sq (n : ℝ)]
  -- `t ≤ τ` are the time of the solver and its bound, `ℓ = log (3nu)`, `c` is the number of rounds
  -- and `s = n²`
  generalize (Tn n (3 * (n * U)) : ℝ) = t at hτ ⊢
  generalize T n (3 * ((n : ℝ) * u)) = τ at hτ hτ0 ⊢
  generalize logU (3 * ((n : ℝ) * u)) = ℓ at hsℓ ⊢
  generalize (Nat.clog 2 n : ℝ) = c at hc0 ⊢
  generalize (n : ℝ) ^ 2 = s at hns hs1 hsℓ ⊢
  have hround : t + 23 * s + 29 ≤ τ + 135 * (s * (1 + ℓ)) := by linarith
  have hends : 53 * s + 17 * n + 65 ≤ τ + 135 * (s * (1 + ℓ)) := by linarith
  calc c * (t + 23 * s + 29) + 53 * s + 17 * n + 65
      ≤ c * (τ + 135 * (s * (1 + ℓ))) + (τ + 135 * (s * (1 + ℓ))) := by
        linarith [mul_le_mul_of_nonneg_left hround hc0]
    _ = (c + 1) * (τ + 135 * (s * (1 + ℓ))) := by ring

end Light.Sec3

end
end


theorem solution : ThreeSumApsp.Claim.ApspFromMinPlus Light.lightModel := by
  exact @Light.Sec3.claim_apspFromMinPlus_sourceProof

#print axioms solution
