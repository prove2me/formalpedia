-- Prove2me | solution 1 for Light.Sec4.pre31_program31
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:40:24.209466+00:00
-- url     : https://prove2.me/submissions/d578544e-bc2a-41d8-8694-6ee4c6f20691

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Lemma6
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Lemma7_8
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Iterate
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Sec2_sharedCallees_of_prefix
import Theorems.Thm_Light_Sec4_specs40

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
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

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























theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h))
      hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim

/-- **Blocks.**  A block that runs safely from σ ends within any T ≥ s.blockCost, in the state
s.after σ. -/
theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by first
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
                                        | ((ring_nf); (omega)))) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

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

/-- A piece of the program about which `h` is known, followed by the rest of the program, which gets
the steps that are left. -/
theorem Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
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
  Ends.next T₁ (h.mono le_rfl rest) hT

/-- A piece of the program about which `h` is known, at the end of the program. -/
theorem Ends.pieceLast {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s σ T₁ R) (rest : ∀ σ', R σ' → Q σ') (hT : T₁ ≤ T := by first
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
    Ends lim P d s σ T Q :=
  h.mono hT rest















/-- A store at the end of the program. -/
theorem Ends.storeLast {loc μ : ℕ → ℤ} {T : ℕ} {a e : Expr} {Q : State → Prop}
    (h : Q ⟨loc, Function.update μ (a.val ⟨loc, μ⟩).toNat (e.val ⟨loc, μ⟩)⟩)
    (hs : a.Safe lim ⟨loc, μ⟩ ∧ e.Safe lim ⟨loc, μ⟩ ∧ lim.Addr (a.val ⟨loc, μ⟩) := by (((try have := Light.Std.space_le (by assumption)));
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
                                                | ((ring_nf); (omega)))) : Ends lim P d (.store a e) ⟨loc, μ⟩ T Q :=
  Ends.store hs.1 hs.2.1 hs.2.2 hT h

/-- A store, followed by the rest of the program. -/
theorem Ends.storeThen {loc μ : ℕ → ℤ} {T : ℕ} {a e : Expr} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s ⟨loc, Function.update μ (a.val ⟨loc, μ⟩).toNat (e.val ⟨loc, μ⟩)⟩
      (T - (a.cost + e.cost + 1)) Q)
    (hs : a.Safe lim ⟨loc, μ⟩ ∧ e.Safe lim ⟨loc, μ⟩ ∧ lim.Addr (a.val ⟨loc, μ⟩) := by (((try have := Light.Std.space_le (by assumption)));
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
    Ends lim P d ((Light.Stmt.seq (.store a e) s)) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.storeLast h hs le_rfl) hT

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

/-- **Loops whose body is a block.**  I j is the invariant before round j of n rounds.  The time is
computed from body.blockCost. -/
theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by first
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
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

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

/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR

/-- A specification whose time is a constant times a shape holds for every larger constant. -/
theorem Meets.mono_const {c c' S : ℕ} (h : Meets lim P p d vals μ (c * S) R) (hc : c ≤ c') :
    Meets lim P p d vals μ (c' * S) R :=
  h.mono_time (Nat.mul_le_mul_right _ hc)







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

theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl








/-- Two steps that keep different cells. -/
theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)

/-- Writing a cell that need not be kept. -/
theorem SameOn.write (h : SameOn K μ μ') (hb : ¬ K b) (x : ℤ) :
    SameOn K μ (Function.update μ' b x) := fun c hc => by
  rw [Function.update_of_ne (by rintro rfl; exact hb hc)]; exact h c hc

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

































/-! ## The next index -/























end Nat

namespace Int

/-! ## Residues as natural numbers -/










end Int

end
end

section


/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}












@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)

/-- Reading a cell of a segment. -/
theorem Seg.get (h : Seg μ a l) {i : ℕ} (hi : i < l.length) : μ (a + i) = l[i] := h i hi









theorem seg_cons : Seg μ a (x :: l) ↔ μ a = x ∧ Seg μ (a + 1) l := by
  constructor
  · intro h
    refine ⟨by have h0 := h 0 (by simp); rwa [Nat.add_zero, List.getElem_cons_zero] at h0,
      fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := h i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

























/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_44549_0 apspMacro_44549_1);
                                                                                  (first
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_44549_2));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_44549_2 apspMacro_44549_0 (by omega)));
                                                                                                  (revert apspMacro_44549_2)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((simp [] at apspMacro_44549_1);
                                                                                        (((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_44549_3));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_44549_3 apspMacro_44549_0 (by omega)));
                                                                                                  (revert apspMacro_44549_3)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_44549_4));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_44549_4 apspMacro_44549_0 (by omega)));
                                                                                                  (revert apspMacro_44549_4)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (fail
                                                                                            "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                      its condition K x does not follow from the hypotheses."))))) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩























theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl






/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc

















/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]




































/-- A matrix stays where it is if its cells do not change. -/
theorem MatAt.congr {n k : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (he : ∀ b, a ≤ b → b < a + n * k → μ' b = μ b) : MatAt μ' a A := fun i j => by
  have := Nat.mul_add_lt_mul i.isLt j.isLt
  rw [he _ (by omega) (by omega)]
  exact h i j






/-- A matrix that lies below e is still there in a memory that agrees below e. -/
theorem MatAt.congr_below {n k e : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hlow : ∀ x < e, μ' x = μ x) (hle : a + n * k ≤ e) : MatAt μ' a A :=
  h.congr fun b _ hb => hlow b (by omega)
















end Light

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







/-- **The rule for a pass.**  The locals x and y hold the length n and the address dst.  In round j
the locals are the given ones with j in the counter, and the memory is `wrote μ dst f j`; there the
expression e has to be safe and have the value f j. -/
theorem Ends.pass {c x y n T : ℕ} {e : Expr} {loc : ℕ → ℤ} {Q : State → Prop} (f : ℕ → ℤ)
    (round : ∀ j < n, e.Safe lim ⟨Function.update loc c j, wrote μ dst f j⟩ ∧
      e.val ⟨Function.update loc c j, wrote μ dst f j⟩ = f j)
    (done : Q ⟨Function.update loc c n, wrote μ dst f n⟩)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) (hlen : loc x = n)
    (haddr : loc y = dst) (hx : x ≠ c := by decide) (hy : y ≠ c := by decide)
    (hT : n * (e.cost + 12) + 6 ≤ T := by first
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
    Ends lim P d (pass c (v x) (v y) e) ⟨loc, μ⟩ T Q := by
  refine Ends.forMem (fun j μ' => μ' = wrote μ dst f j) n _ wrote_zero.symm
    (fun j μ' hj hμ' => Ends.block ?round le_rfl)
    (fun μ' h => by rw [h]; exact done)
    (fun j μ' _ _ => ⟨trivial, (Function.update_of_ne hx _ _).trans hlen⟩) (by omega)
    (le_trans (le_of_eq (by simp only [Stmt.blockCost, Expr.cost]; ring)) hT)
  -- Round j: dst[j] := e.
  subst hμ'
  obtain ⟨hs, hv⟩ := round j hj
  have qc : Function.update loc c (j : ℤ) c = j := Function.update_self ..
  have qy : Function.update loc c (j : ℤ) y = dst := by rw [Function.update_of_ne hy, haddr]
  refine ⟨⟨?_, hs, ?_⟩, rfl, ?_⟩
  · simp only [Expr.Safe, Expr.val, Op.eval, qc, qy, true_and, abs_le]
    omega
  · simp only [Expr.val, Op.eval, qc, qy, Limits.Addr]
    omega
  · simp only [Stmt.after, Expr.val, Op.eval, qc, qy, hv, toNat_natCast_add_natCast, wrote_succ]

end Light

end
end

section


/-!
# Copying and filling a segment

copy(src, dst, n) copies n cells from src to dst (the two segments do not overlap), within
`copyTime n` steps.  fill(dst, n, x) writes x into n cells from dst, within `fillTime n` steps.
Both change no other cell (`copy_meets`, `fill_meets`).  Each of the two is one pass over the cells
from dst, so `Ends.pass` says what it does, and the proof only says what round i reads.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## copy -/

namespace Copy







end Copy








/-- **copy(src, dst, n)** copies the n cells from src to dst and changes nothing else. -/
theorem copy_meets {p : ℕ} (hp : P[p]? = some copyBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n ≤ lim.space) (hdst : dst + n ≤ lim.space)
    (hsep : Apart src n dst n) :
    Meets lim P p d [(src : ℤ), dst, n] μ (copyTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ SameOutside μ μ' dst n := by
  refine .of_body hp (Ends.pass (fun i => μ (src + i)) (fun i hi => ?_)
    ⟨fun i hi => wrote_done (f := fun i => μ (src + i)) hi, by ((try refine Light.SameOn.cell ?_); (intro apspMacro_49825_0 apspMacro_49825_1);
                                                                    (first
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_49825_2));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_49825_2 apspMacro_49825_0 (by omega)));
                                                                                    (revert apspMacro_49825_2)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((simp [] at apspMacro_49825_1);
                                                                          (((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_49825_3));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_49825_3 apspMacro_49825_0 (by omega)));
                                                                                    (revert apspMacro_49825_3)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_49825_4));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_49825_4 apspMacro_49825_0 (by omega)));
                                                                                    (revert apspMacro_49825_4)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (fail
                                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                        its condition K x does not follow from the hypotheses."))))⟩ hw hdst rfl rfl
    (hT := by first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, copyTime]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [copyTime] <;>
                    first
                    | omega
                    | ((ring_nf); (omega)))))
  -- Round i reads src[i], which no earlier round has written.
  have hread : wrote μ dst (fun i => μ (src + i)) i (src + i) = μ (src + i) :=
    wrote_rest (by omega)
  (((try have := Light.Std.space_le (by assumption)));
    ((try have := Light.Std.const_le (by assumption)));
    (simp [Light.Limits.Addr, abs_le, -abs_mul, hread] <;> omega))

/-! ## fill -/

namespace Fill







end Fill








/-- **fill(dst, n, x)** writes x into the n cells from dst and changes nothing else. -/
theorem fill_meets {p : ℕ} (hp : P[p]? = some fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    Meets lim P p d [(dst : ℤ), n, x] μ (fillTime n) fun _ μ' =>
      Seg μ' dst (List.replicate n x) ∧ SameOutside μ μ' dst n :=
  .of_body hp (Ends.pass (fun _ => x) (fun i hi => by (((try have := Light.Std.space_le (by assumption)));
                                                        ((try have := Light.Std.const_le (by assumption)));
                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by ((try refine Light.SameOn.cell ?_); (intro apspMacro_50692_0 apspMacro_50692_1);
                                                                                   (first
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_50692_2));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_50692_2 apspMacro_50692_0 (by omega)));
                                                                                                   (revert apspMacro_50692_2)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((simp [] at apspMacro_50692_1);
                                                                                         (((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_50692_3));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_50692_3 apspMacro_50692_0 (by omega)));
                                                                                                   (revert apspMacro_50692_3)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_50692_4));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_50692_4 apspMacro_50692_0 (by omega)));
                                                                                                   (revert apspMacro_50692_4)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (fail
                                                                                             "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                       its condition K x does not follow from the hypotheses."))))⟩
    hw hdst rfl rfl (hT := by first
                              |
                                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, fillTime]);
                                  (first
                                    | omega
                                    | ((ring_nf); (omega))))
                              | omega
                              |
                                (simp [fillTime] <;>
                                    first
                                    | omega
                                    | ((ring_nf); (omega)))))

end Light

end
end

section


/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}




@[simp] theorem length_powList (b L : ℕ) : (powList b L).length = L := by simp [powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (powList b L).length) :
    (powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [powList]

namespace PowTable









end PowTable

open PowTable




































































end Light

end
end

section


/-!
# Theorem 5 in the light language: sizes and places

The sizes of the tables and arrays of Theorem 5's program, and their places in the memory. No
program occurs here.

The program for Theorem 5 (the solver) and the data structure of Section 4 begin with the same
stage, the shared stage, which fills the shared block: a directory of 32 cells with the sizes and
the addresses of the areas (`dirList`), then the tables, then the encodings of all bands, then two
scratch areas. The solver has a private block behind it. The areas lie one after the other:
`Par.places` (the shared block) and `Par.places5` (the private block) say where every area begins
and ends. `Par.sizes` collects the inequalities between the sizes, each of which has a name of its
own.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Sizes -/











namespace Par






















/-! ## The shared block, from its base address `b0` on -/











































end Par








/-! ## The private block of Theorem 5

The solver receives `N`, `D`, the number `w` of wanted positions, a bound `U` on the entries, the
addresses of `X`, `Y` (row by row), of the rows `WI` and the columns `WJ` of the wanted positions
and of the output, and as last argument the free pointer `fr`. All inputs and the output lie below
`fr`. The solver may write the output and the cells from `fr` on, and nothing is assumed about these
cells: a routine clears what it needs cleared. The shared block starts at `fr`, the private block
follows it. -/

namespace Par




























end Par

/-! ## The places and the sizes, as equations and inequalities -/

/-- The places of the shared block: each area begins where the one before it ends. -/
theorem Par.places (p : Par) (b0 : ℕ) :
    p.aDIR b0 = b0 ∧ p.aP3 b0 = b0 + 32 ∧ p.aP4 b0 = p.aP3 b0 + (p.L + 1)
      ∧ p.aP7 b0 = p.aP4 b0 + (p.L + 1)
      ∧ p.aP10 b0 = p.aP7 b0 + (p.L + 1) ∧ p.aPAS b0 = p.aP10 b0 + (p.L + 1)
      ∧ p.aPHI b0 = p.aPAS b0 + (p.L + 2) ∧ p.aPSI b0 = p.aPHI b0 + 70
      ∧ p.aMASK b0 = p.aPSI b0 + 70 ∧ p.aBAND b0 = p.aMASK b0 + p.KK * p.L
      ∧ p.aBLOCK b0 = p.aBAND b0 + p.N ∧ p.aDIG3 b0 = p.aBLOCK b0 + p.N
      ∧ p.aDIG4 b0 = p.aDIG3 b0 + p.N * p.Lo ∧ p.aENCA b0 = p.aDIG4 b0 + p.D * p.m
      ∧ p.aENCB b0 = p.aENCA b0 + p.nB * p.T ∧ p.aARR b0 = p.aENCB b0 + p.nB * p.T
      ∧ p.aZS b0 = p.aARR b0 + p.S7 ∧ p.sharedEnd b0 = p.aZS b0 + p.S7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Par
variable (p : Par)

theorem one_le_T : 1 ≤ p.T := Nat.one_le_pow _ _ (by omega)

theorem L_lt_T : p.L < p.T := Nat.lt_pow_self (by omega)

/-- `2^L ≤ 10^L`. -/
theorem two_pow_le_T : 2 ^ p.L ≤ p.T := Nat.pow_le_pow_left (by omega) _

theorem K_le_T : p.K ≤ p.T := (Nat.choose_le_two_pow _ _).trans p.two_pow_le_T

theorem N0_le_T : p.N0 ≤ p.T :=
  (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))

theorem D_le_T (hmL : p.m ≤ p.L) : p.D ≤ p.T :=
  (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hmL)

theorem K0_le_K : p.K0 ≤ p.K := Nat.sqrt_le_self _

/-- `K₀² ≤ K`. -/
theorem KK_le_K : p.KK ≤ p.K := Nat.sqrt_le _

/-- The sizes: 1, `L`, `2^L`, `K`, `N₀` and `D` are at most `T = 10^L`; `K₀` and `K₀²` are at most
`K`; `K₀` and `N₀` are positive; and the definition of `Lo`. -/
theorem sizes (hmL : p.m ≤ p.L) :
    1 ≤ p.T ∧ p.L < p.T ∧ 2 ^ p.L ≤ p.T ∧ p.K ≤ p.T ∧ p.N0 ≤ p.T ∧ p.D ≤ p.T ∧ p.K0 ≤ p.K
      ∧ p.KK ≤ p.K ∧ 0 < p.K0 ∧ 0 < p.N0 ∧ p.Lo = p.L - p.m :=
  ⟨p.one_le_T, p.L_lt_T, p.two_pow_le_T, p.K_le_T, p.N0_le_T, p.D_le_T hmL, p.K0_le_K, p.KK_le_K,
    ThreeSumApsp.K0_pos hmL, ThreeSumApsp.N0_pos _ _, rfl⟩

end Par











end Light.Sec2

end
end

section


/-!
# Lemma 6: Schönhage's identity

Sections 2.1 and 2.2. After Strassen's identity (equation (1)), which the paper
recalls, this file treats Schönhage's. It has ten terms `λ`, each the product of a linear form `φ_λ`
in the seven left variables, a linear form `ψ_λ` in the seven right variables and a linear form
`χ_λ` in the ten output variables. Lemma 6 says that `∑_λ φ_λ ψ_λ χ_λ = G + E`, an identity of
polynomials in the 24 variables: `G` holds the outer product and the inner product that are wanted,
and `E` is an error.

* A linear form is the vector of its coefficients. `formL`, `formR` and `formO` turn it into a
  polynomial, and they are linear (`formL_eq_linearCombination` and its two companions).
* The proof of `lemma_6` is the paper's. The coefficient of `z_ij` comes only from the term `P_ij`.
  In the coefficient of `z₀` the products `x_i y_j` cancel, the cross terms vanish because the
  columns of `p̂` and the rows of `q̂` sum to zero (`pHat_column_sum`, `qHat_row_sum`), and what
  remains is the inner product (`sum_pHat_mul_qHat`).
* Second observation after the lemma: every term contributes to `z₀`, and only `P_ij` contributes to
  `z_ij` (`Term.contributes_z0`, `Term.contributes_z_iff`).

The later files on Section 2 use the second observation and the coefficients of the forms; none of
their proofs uses `lemma_6`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp















/-! ### The alphabets -/


































/-- Section 2.2: there are "seven left variables". -/
theorem card_leftVar : Fintype.card LeftVar = 7 := by
  simp [Fintype.card_congr LeftVar.equiv]

/-- Section 2.2: there are "seven right variables". -/
theorem card_rightVar : Fintype.card RightVar = 7 := by
  simp [Fintype.card_congr RightVar.equiv]











/-! ### Linear forms as polynomials -/























































/-! ### Lemma 6 -/



































/-! ### Which terms contribute to which output variables -/




































end ThreeSumApsp

end
end

section


/-!
# The alphabets of Schönhage's identity as digits

Section 2.2 names seven left variables, seven right variables, ten output variables and
ten terms; Section 2.3.1 indexes arrays by strings over these alphabets.  Here every
letter gets a digit, so that a string becomes a number (`codeStr`).

* The left variables `x₁ x₂ x₃ p₁₁ p₁₂ p₂₁ p₂₂` are the digits `0, …, 6`; likewise the right
  variables.
* The output variables `z₁₁ z₁₂ … z₃₃ z₀` are the digits `0, …, 9`, and the terms `P₁₁ … P₃₃ P₀`
  likewise, so that `z_ij` and `P_ij` have the same digit `3(i-1) + (j-1)`, and `z₀` and `P₀` have
  the digit 9.
* Left and right strings are numbers in base 7 (`codeL`, `codeR`), output strings, vertices and
  leaves in base 10 (`codeO`, `codeT`), strings of indices of outer variables in base 3
  (`codeOuter`) and of inner variables in base 4 (`codeInner`), always with level 1 most
  significant.
* Which output variables are inner, and which term contributes to which output variable (Section
  2.2), is read off the digits (`outVar_isInner_iff`, `contributes_iff`).
* The coefficients of the linear forms `φ_λ` and `ψ_λ` (Section 2.2) are written out as the rows of
  two 10 × 7 tables, `phiTable` and `psiTable`, which the programs store row after row
  (`phiFlat_spec`, `psiFlat_spec`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Digits -/





























































































/-! Applying one of the five bijections gives the digit. -/











/-! ## Codes of strings -/

























/-! ### Codes of output strings and of vertices

The general facts about `codeStr`, under names of their own for the two codes that occur most. -/




































/-! ## The structure of the identity, in digits -/

































/-! ## The coefficients of the linear forms, as tables -/





















/-- The table of the `φ_λ(s)` has 70 entries. -/
@[simp] theorem length_phiFlat : phiFlat.length = 70 := rfl

/-- The table of the `ψ_λ(t)` has 70 entries. -/
@[simp] theorem length_psiFlat : psiFlat.length = 70 := rfl













end ThreeSumApsp.Spec

end
end

section


/-!
# Arrays on strings as lists

Section 2.3.1: "An array a on the left strings of length L assigns an integer a[u] to each u that is
a left string of length L."  In a program such an array is a list: an array on the strings of length
`n` over an alphabet of `b` letters is the list of its `b^n` entries in the order of the codes
(`arrStr`), so the entry at a string is the entry of the list at the code of the string
(`getD_arrStr`), and an entry of the list is 0 if the array is 0 at the string with that code
(`getD_arrStr_eq_zero`).  The arrays on left strings, on right strings and on leaves are the cases
`arrL`, `arrR` and `arrT`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Arrays on the strings over any numbered alphabet -/

section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)






/-- The list has `b^n` entries. -/
theorem length_arrStr : (arrStr e a).length = b ^ n := by
  simp [arrStr]



















end

/-! ## The three kinds of arrays of Section 2 that the programs store -/


















/-- The list of an array on the leaves has `10^n` entries. -/
theorem length_arrT {n : ℕ} (enc : Leaf n → ℤ) : (arrT enc).length = 10 ^ n :=
  length_arrStr termEquiv enc















end ThreeSumApsp.Spec

end
end

section


/-!
# The memory map of Theorem 5: what depends on which cells

SharedReady.dirs lists the cells of the directory that the solver reads. SharedTables are the tables
of the shared block without the directory and the encodings; they depend only on the cells between
these two (SharedTables.congr), and all that the shared stage leaves behind depends only on the
cells of the shared block, without the last of the 32 cells of the directory, which the shared stage
does not use (SharedReady.congr, SharedReady.of_agree).
-/

public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The directory -/

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- Cell j of the directory, with the address in the form in which the evaluation of mem[b0 + j]
meets it. -/
theorem SharedReady.dir_read (h : SharedReady p hmL aX aY b0 X Y μ) {j : ℕ} (hj : j < 31) :
    μ ((b0 : ℤ) + j).toNat = ((dirList p aX aY b0).getD j 0 : ℕ) := by
  rw [toNat_natCast_add_natCast]
  exact h.dir.read (by simpa [dirList] using hj)
















/-! ## Only the shared block matters -/

/-- The tables lie between the directory and the encodings: they are still there in a memory that
agrees on these cells. -/
theorem SharedTables.congr {p : Par} {b0 : ℕ} {μ μ' : ℕ → ℤ} (h : SharedTables p b0 μ)
    (he : ∀ x, p.aP3 b0 ≤ x → x < p.aENCA b0 → μ' x = μ x) : SharedTables p b0 μ' := by
  have hplaces := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  have lphi := Spec.length_phiFlat
  have lpsi := Spec.length_psiFlat
  refine
    { p3 := h.p3.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p4 := h.p4.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p7 := h.p7.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p10 := h.p10.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      phi := h.phi.congr fun i hi => he _ (by omega) (by omega)
      psi := h.psi.congr fun i hi => he _ (by omega) (by omega)
      mask := fun s hs => (h.mask s hs).congr fun i hi => he _ (by omega) ?_
      band := fun I hI => (he _ (by omega) (by omega)).trans (h.band I hI)
      block := fun I hI => (he _ (by omega) (by omega)).trans (h.block I hI)
      dig3 := fun I hI => (h.dig3 I hI).congr fun i hi => he _ (by omega) ?_
      dig4 := fun x hx => (h.dig4 x hx).congr fun i hi => he _ (by omega) ?_ }
  · rw [List.length_map, Spec.length_unrank] at hi
    have := Nat.mul_add_lt_mul hs hi
    omega
  · have := Nat.mul_add_lt_mul hI (show i < p.Lo by simpa [ThreeSumApsp.digitList] using hi)
    omega
  · have := Nat.mul_add_lt_mul hx (show i < p.m by simpa [ThreeSumApsp.digitList] using hi)
    omega

/-- What the shared stage leaves behind is kept by a memory that agrees on the cells of the shared
block, but for cell 31 of the directory, which the shared stage does not use. -/
theorem SharedReady.congr (h : SharedReady p hmL aX aY b0 X Y μ)
    (hag : ∀ a, b0 ≤ a → a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReady p hmL aX aY b0 X Y μ' := by
  have hplaces := p.places b0
  have tb : SharedTables p b0 μ' :=
    h.toSharedTables.congr fun x hlo hx => hag x (by omega) (by omega) (by omega)
  have henc : ∀ {a β i : ℕ}, p.aENCA b0 ≤ a → a + p.nB * p.T ≤ p.sharedEnd b0 → β < p.nB →
      i < p.T → μ' (a + β * p.T + i) = μ (a + β * p.T + i) := fun ha hend hβ hi => by
    have := Nat.mul_add_lt_mul hβ hi
    exact hag _ (by omega) (by omega) (by omega)
  refine
    { tb with
      dir := h.dir.congr fun i hi => ?_
      encA := fun β hβ => (h.encA β hβ).congr fun i hi =>
        henc le_rfl (by omega) hβ (by rwa [Spec.length_arrT] at hi)
      encB := fun β hβ => (h.encB β hβ).congr fun i hi =>
        henc (by omega) (by omega) hβ (by rwa [Spec.length_arrT] at hi) }
  simp only [dirList, List.length_map, List.length_cons, List.length_nil] at hi
  simp only [Par.aDIR]
  exact hag _ (by omega) (by omega) (by omega)

/-- What the shared stage leaves behind is kept by a memory that agrees on all cells below the end
of the shared block, but for cell 31 of the directory. -/
theorem SharedReady.of_agree (h : SharedReady p hmL aX aY b0 X Y μ)
    (hag : ∀ a, a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReady p hmL aX aY b0 X Y μ' :=
  h.congr fun a _ => hag a

end Light.Sec2

end
end

section


/-!
# Strings, vertices and the coefficients of the encoding

Section 2.3.1. The recursion `Full` works on arrays indexed by strings of variables. This file has
the counts that the later cost estimates use: `7^L` left strings and `7^L` right strings of length
`L`, `10^k` vertices at depth `k` of the recursion tree, and coefficients `φ_λ(s)` and `ψ_λ(t)` in
`{0, ±1}`. The first three follow from the sizes of the alphabets; the last is a finite check. So is
the sentence that each form has at most three nonzero coefficients (`card_support_phi_le`,
`card_support_psi_le`), which no later proof uses. The example in the caption of Figure 3 is
`figure_3`.
-/

public section

open Finset

namespace ThreeSumApsp

/-- Section 2.3.1: an array on the left strings of length `L` "has 7^L entries in total". -/
theorem card_leftStr (L : ℕ) : Fintype.card (LeftStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_leftVar, Fintype.card_fin]

/-- Section 2.3.1: an array on the right strings of length `L` has `7^L` entries. -/
theorem card_rightStr (L : ℕ) : Fintype.card (RightStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_rightVar, Fintype.card_fin]





/-- Section 2.3.1: "φ_λ(s) ∈ {0, ±1}". -/
theorem abs_phi_le_one (lam : Term) (s : LeftVar) : |phi lam s| ≤ 1 := by
  decide +revert

/-- Section 2.3.1: `ψ_λ(t) ∈ {0, ±1}`. -/
theorem abs_psi_le_one (lam : Term) (t : RightVar) : |psi lam t| ≤ 1 := by
  decide +revert



























end ThreeSumApsp

end
end

section


/-!
# Bounds on finite sums and products

General facts about sums and products over a finite set in an ordered ring or field.

* A sum of `s.card` numbers of absolute value at most `A` is at most `s.card * A` in absolute value
  (`Finset.abs_sum_le_card_mul`), also with coefficients of absolute value at most `1`
  (`Finset.abs_sum_mul_le`).
* A product of numbers of absolute value at most `1` has absolute value at most `1`
  (`Finset.abs_prod_le_one`). For integers, `Int.abs_le_one_iff` says that these are `0`, `1`, `-1`.
* A sum over the indices below `m * n` is a double sum (`Finset.sum_range_mul`).
* A part of a geometric series with ratio `0 < x < 1` is less than the whole series from its first
  term on (`geom_sum_Ico_lt_of_lt_one`).
-/

public section

namespace Finset

variable {ι R : Type*}

/-- If `|f i| ≤ A` for all `i ∈ s`, then `|∑ i ∈ s, f i| ≤ s.card * A`. -/
theorem abs_sum_le_card_mul [Ring R] [LinearOrder R] [IsOrderedRing R] (s : Finset ι) {f : ι → R}
    {A : R} (h : ∀ i ∈ s, |f i| ≤ A) : |∑ i ∈ s, f i| ≤ s.card * A :=
  (abs_sum_le_sum_abs f s).trans ((sum_le_card_nsmul s _ A h).trans_eq (nsmul_eq_mul _ _))

/-- If `|c i| ≤ 1` and `|a i| ≤ A` for all `i ∈ s`, then `|∑ i ∈ s, c i * a i| ≤ s.card * A`. -/
theorem abs_sum_mul_le [Ring R] [LinearOrder R] [IsOrderedRing R] (s : Finset ι) {c a : ι → R}
    {A : R} (hc : ∀ i ∈ s, |c i| ≤ 1) (ha : ∀ i ∈ s, |a i| ≤ A) :
    |∑ i ∈ s, c i * a i| ≤ s.card * A :=
  abs_sum_le_card_mul s fun i hi =>
    (abs_mul (c i) (a i)).trans_le
      ((mul_le_of_le_one_left (abs_nonneg _) (hc i hi)).trans (ha i hi))

/-- If `|f i| ≤ 1` for all `i ∈ s`, then `|∏ i ∈ s, f i| ≤ 1`. -/
theorem abs_prod_le_one [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι)
    {f : ι → R} (h : ∀ i ∈ s, |f i| ≤ 1) : |∏ i ∈ s, f i| ≤ 1 :=
  (abs_prod s f).trans_le (prod_le_one (fun _ _ => abs_nonneg _) h)









end Finset













end
end

section


/-!
# Section 2.4.4: the remaining minutiae and the word size

* Minutiae.  The `K₀²` subsets, the tiles and the positions of `W` number `O(N² / D^{1/18})` in all
  (`minutiae_total_le`), because `K ≤ N` (`K_le_of_D_pow_le`), there are at most `4N²/N₀` tiles
  (`card_tiles_mul_N0_le`), `|W| ≤ 2^{-m} N²`, and `N, N₀ ≥ 2^{m/9}` (`two_rpow_le_of_D_pow_le`,
  `two_rpow_le_N0`).
* Word size.  An entry of an input array is an entry of `X` or `Y` or 0 (`abs_bandArrayL_le`,
  `abs_bandArrayR_le`); an encoded number is a `±1` combination of at most `7^L` of them
  (`abs_encodingL_le`, `abs_encodingR_le`); a value of `Pruned` is a sum of at most `10^L` products
  of two encoded numbers (`abs_Pruned_le`); and `10^L ≤ N²` by equation (6) (`ten_pow_le_sq`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The remaining minutiae -/






























































































/-! ### The word size -/

/-- The subsets in the table are distinct (Section 2.3.4), so a sum over the table that selects the
subset `Q` is one of its terms or 0. -/
private theorem sum_table_eq_zero_or {L m : ℕ} {A : Type*} [AddCommMonoid A] (lay : Layout L m)
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (Q : Finset (Fin L)) :
    (∑ gh, if lay.table gh = Q then F gh else 0) = 0
      ∨ ∃ gh, (∑ gh', if lay.table gh' = Q then F gh' else 0) = F gh := by
  by_cases hQ : ∃ gh, lay.table gh = Q
  · obtain ⟨gh, rfl⟩ := hQ
    exact .inr ⟨gh, by simp [lay.table_injective.eq_iff]⟩
  · exact .inl (sum_eq_zero fun gh _ => if_neg (not_exists.mp hQ gh))

/-- Section 2.4.4, word size: "The input entries are of this size, by assumption." Every entry of
the input array of a row band is an entry of `X` or 0.

NOTE.  `0 ≤ A` is needed only when `N = 0`. -/
theorem abs_bandArrayL_le {L m N : ℕ} (lay : Layout L m) {X : Matrix (Fin N) (Fin (D m)) ℤ} {A : ℤ}
    (hA : 0 ≤ A) (hX : ∀ I k, |X I k| ≤ A) (β : ℕ) (u : LeftStr L) :
    |bandArrayL lay X β u| ≤ A := by
  unfold bandArrayL arrayL bandFamilyL
  split_ifs with h
  · rcases sum_table_eq_zero_or lay (fun gh => rowBlock lay X (β * K0 L m + gh.1)) (innerSetL u)
      with hzero | ⟨gh, hgh⟩
    · rw [hzero]
      simpa using hA
    · rw [hgh]
      unfold rowBlock padRows
      split_ifs
      · exact hX _ _
      · simpa using hA
  · simpa using hA

/-- Section 2.4.4, word size: "The input entries are of this size, by assumption." Every entry of
the input array of a column band is an entry of `Y` or 0.

NOTE.  `0 ≤ B` is needed only when `N = 0`. -/
theorem abs_bandArrayR_le {L m N : ℕ} (lay : Layout L m) {Y : Matrix (Fin (D m)) (Fin N) ℤ} {B : ℤ}
    (hB : 0 ≤ B) (hY : ∀ k J, |Y k J| ≤ B) (β : ℕ) (v : RightStr L) :
    |bandArrayR lay Y β v| ≤ B := by
  unfold bandArrayR arrayR bandFamilyR
  split_ifs with h
  · rcases sum_table_eq_zero_or lay (fun gh => colBlock lay Y (β * K0 L m + gh.2)) (innerSetR v)
      with hzero | ⟨gh, hgh⟩
    · rw [hzero]
      simpa using hB
    · rw [hgh]
      unfold colBlock padCols
      split_ifs
      · exact hY _ _
      · simpa using hB
  · simpa using hB

/-- A combination of the entries of an array, with a product of coefficients 0, 1 or -1 for each
entry, is at most the number of entries times the largest absolute value of an entry. -/
theorem abs_encodeWith_le {α : Type} [Fintype α] {c : Term → α → ℤ} (hc : ∀ lam s, |c lam s| ≤ 1)
    {L : ℕ} {a : (Fin L → α) → ℤ} {A : ℤ} (ha : ∀ u, |a u| ≤ A) (τ : Leaf L) :
    |encodeWith c τ a| ≤ Fintype.card (Fin L → α) * A := by
  have h := abs_sum_mul_le univ (c := fun u => ∏ ℓ, c (τ ℓ) (u ℓ))
    (fun u _ => abs_prod_le_one _ fun ℓ _ => hc _ _) fun u _ => ha u
  simpa only [encodeWith, mul_comm, card_univ] using h

/-- Section 2.4.4, word size: "Every number in an encoding […] is a ±1 combination of at most 7^L
input entries", so its absolute value is at most `7^L` times the largest absolute value of an input
entry.  For the encoding of `a`. -/
theorem abs_encodingL_le {L : ℕ} {a : LeftStr L → ℤ} {A : ℤ} (ha : ∀ u, |a u| ≤ A) (τ : Leaf L) :
    |encodingL a τ| ≤ 7 ^ L * A := by
  have h := abs_encodeWith_le abs_phi_le_one ha τ
  rw [card_leftStr] at h
  exact_mod_cast h

/-- Section 2.4.4, word size: "Every number in an encoding […] is a ±1 combination of at most 7^L
input entries".  For the encoding of `b`. -/
theorem abs_encodingR_le {L : ℕ} {b : RightStr L → ℤ} {B : ℤ} (hb : ∀ v, |b v| ≤ B) (τ : Leaf L) :
    |encodingR b τ| ≤ 7 ^ L * B := by
  have h := abs_encodeWith_le abs_psi_le_one hb τ
  rw [card_rightStr] at h
  exact_mod_cast h





































end ThreeSumApsp

end
end

section


/-!
# The encodings of all bands of one matrix (Section 2.4.1)

Section 2.4.1: "We compute the encodings of the input arrays of all row bands and all column bands
[...], and every tile reads its two encodings from these."  encodeBands does this for one of the two
matrices: for each band β it calls bandArray, which forms the input array of the band at arr, and
encode, which leaves its encoding in the T = 10^L cells from enc + β T.

The loop is treated once, for callees that are described by what they do here (`encodeBands_proc`).
The two entries, for the row bands of X and for the column bands of Y, put in the specifications of
bandArray and encode for their side.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

namespace Bands

































end Bands

























/-! ## The arguments, and what is assumed about them -/































variable {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ μ' : ℕ → ℤ}


















































/-! ## What is read does not change -/
























/-- The tables also lie below every larger bound. -/
theorem BandTables.mono {p : Par} {μ : ℕ → ℤ} {mask dig3 dig4 e e' : ℕ}
    (h : BandTables p μ mask dig3 dig4 e) (hle : e ≤ e') : BandTables p μ mask dig3 dig4 e' :=
  { h with
    mask_le := h.mask_le.trans hle
    dig3_le := h.dig3_le.trans hle
    dig4_le := h.dig4_le.trans hle }




















/-! ## The two entries -/

































































end Light.Sec2

end
end

section


/-!
# The shared stage: everything up to the encodings of all bands

shared(L, m, N, D, aX, aY, b0) fills the shared block of the memory map: the tables of powers, the
coefficients φ and ψ of Schönhage's identity (Section 2.2), the table of the K₀² subsets (Section
2.3.4), band, block and digits of every row, the digits of every column, the encodings of all row
bands of X and of all column bands of Y (Section 2.4.1), and the directory. Theorem 5 and the data
structure of Section 4 both start with it.

The body is a straight line of 36 statements and the 31 stores of the directory. It is cut into
three parts (sharedA, sharedB, sharedC). For each part there are two lemmas: one runs the text
(sharedA_spec, sharedB_spec, sharedC_spec), and one, about memories only, says that what the calls
have written is all there at the end, because each call writes above the areas of the calls before
it (SharedA.of_calls, SharedB.of_calls, SharedReady.of_calls). shared_entry puts the parts together:
if every callee meets its entry with the constant c, then shared runs within 12 c + 600 times
sharedShape (sharedTime_le). The places of the areas are those of Par.places, and their sizes those
of Par.sizes.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

/-! ## The local variables -/

namespace Shared




































































end Shared

open Shared

/-! ## The text -/






/-- **storeLocals** writes the values of the locals to the cells from base + i on, changes nothing
else, and takes 5 steps for each. -/
theorem storeLocals_spec {d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) {base : ℕ} (loc : ℕ → ℤ)
    (hbase : loc Base = base) (xs : List ℕ) :
    ∀ (i : ℕ) (μ : ℕ → ℤ), base + i + xs.length ≤ lim.space →
      Ends lim P d (storeLocals i xs) ⟨loc, μ⟩ (5 * xs.length) fun σ' =>
        Seg σ'.mem (base + i) (xs.map loc) ∧ SameOutside μ σ'.mem (base + i) xs.length := by
  induction xs with
  | nil => exact fun i μ _ => Ends.skip ⟨Seg.nil, SameOutside.refl⟩
  | cons x xs ih =>
    intro i μ hsp
    rw [List.length_cons] at hsp ⊢
    have haddr : ((((Light.Expr.op Light.Op.add) (v Base) (k i))).val ⟨loc, μ⟩).toNat = base + i := by simp [hbase]
    -- mem[base + i] := x
    refine Ends.storeThen ?_ (by (((try have := Light.Std.space_le (by assumption)));
                                   ((try have := Light.Std.const_le (by assumption)));
                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, hbase] <;> omega)))
    rw [haddr]
    refine (ih (i + 1) _ (by omega)).mono (by simp; omega) ?_
    rintro σ' ⟨hs, hf⟩
    refine ⟨seg_cons.2 ⟨?_, by rw [Nat.add_assoc]; exact hs⟩, fun b hb => ?_⟩
    · rw [hf (base + i) (Or.inl (by omega)), Function.update_self]
      rfl
    · rw [hf b (by omega), Function.update_of_ne (by omega)]




















































































































/-- The assumption on the word size, in terms of `T = 10^L`. -/
theorem Par.ten_T_le {p : Par} (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word) :
    10 * (p.T : ℤ) ≤ lim.word := by
  rw [pow_succ, Nat.mul_comm] at h10
  exact_mod_cast h10

/-- What the four calls of the first part leave in the memory: each writes its own area, above the
areas of the calls before it. -/
theorem SharedA.of_calls {p : Par} {b0 : ℕ} {μ μP3 μP4 μP7 μP10 : ℕ → ℤ}
    (sP3 : Seg μP3 (p.aP3 b0) (powList 3 (p.L + 1))) (fP3 : SameOutside μ μP3 (p.aP3 b0) (p.L + 1))
    (sP4 : Seg μP4 (p.aP4 b0) (powList 4 (p.L + 1)))
    (fP4 : SameOutside μP3 μP4 (p.aP4 b0) (p.L + 1))
    (sP7 : Seg μP7 (p.aP7 b0) (powList 7 (p.L + 1)))
    (fP7 : SameOutside μP4 μP7 (p.aP7 b0) (p.L + 1))
    (sP10 : Seg μP10 (p.aP10 b0) (powList 10 (p.L + 1)))
    (fP10 : SameOutside μP7 μP10 (p.aP10 b0) (p.L + 1)) : SharedA p b0 μ μP10 := by
  have hplaces := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  refine
    { p3 := sP3.keep (by ((try have := lp);
                           (((try refine Light.SameOn.cell ?_);
                               (intro apspMacro_79619_0 apspMacro_79619_1);
                               (first
                                 |
                                   ((((repeat
                                             (((with_reducible
                                                     rename Light.SameOn _ _ _ => apspMacro_79619_2));
                                               ((try
                                                     have :=
                                                       apspMacro_79619_2 apspMacro_79619_0 (by omega)));
                                               (revert apspMacro_79619_2)));
                                         (intros);
                                         (try simp only [Function.update_apply, Light.wrote] at *)));
                                     (omega))
                                 |
                                   ((simp [lp] at apspMacro_79619_1);
                                     (((repeat
                                             (((with_reducible
                                                     rename Light.SameOn _ _ _ => apspMacro_79619_3));
                                               ((try
                                                     have :=
                                                       apspMacro_79619_3 apspMacro_79619_0 (by omega)));
                                               (revert apspMacro_79619_3)));
                                         (intros);
                                         (try simp only [Function.update_apply, Light.wrote] at *)));
                                     (omega))
                                 |
                                   ((((repeat
                                             (((with_reducible
                                                     rename Light.SameOn _ _ _ => apspMacro_79619_4));
                                               ((try
                                                     have :=
                                                       apspMacro_79619_4 apspMacro_79619_0 (by omega)));
                                               (revert apspMacro_79619_4)));
                                         (intros);
                                         (try simp only [Function.update_apply, Light.wrote] at *)));
                                     (fail
                                         "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                   SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                   its condition K x does not follow from the hypotheses.")))))))
      p4 := sP4.keep (by ((try have := lp);
                           (((try refine Light.SameOn.cell ?_);
                               (intro apspMacro_79661_0 apspMacro_79661_1);
                               (first
                                 |
                                   ((((repeat
                                             (((with_reducible
                                                     rename Light.SameOn _ _ _ => apspMacro_79661_2));
                                               ((try
                                                     have :=
                                                       apspMacro_79661_2 apspMacro_79661_0 (by omega)));
                                               (revert apspMacro_79661_2)));
                                         (intros);
                                         (try simp only [Function.update_apply, Light.wrote] at *)));
                                     (omega))
                                 |
                                   ((simp [lp] at apspMacro_79661_1);
                                     (((repeat
                                             (((with_reducible
                                                     rename Light.SameOn _ _ _ => apspMacro_79661_3));
                                               ((try
                                                     have :=
                                                       apspMacro_79661_3 apspMacro_79661_0 (by omega)));
                                               (revert apspMacro_79661_3)));
                                         (intros);
                                         (try simp only [Function.update_apply, Light.wrote] at *)));
                                     (omega))
                                 |
                                   ((((repeat
                                             (((with_reducible
                                                     rename Light.SameOn _ _ _ => apspMacro_79661_4));
                                               ((try
                                                     have :=
                                                       apspMacro_79661_4 apspMacro_79661_0 (by omega)));
                                               (revert apspMacro_79661_4)));
                                         (intros);
                                         (try simp only [Function.update_apply, Light.wrote] at *)));
                                     (fail
                                         "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                   SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                   its condition K x does not follow from the hypotheses.")))))))
      p7 := sP7.keep (by ((try have := lp);
                           (((try refine Light.SameOn.cell ?_);
                               (intro apspMacro_79703_0 apspMacro_79703_1);
                               (first
                                 |
                                   ((((repeat
                                             (((with_reducible
                                                     rename Light.SameOn _ _ _ => apspMacro_79703_2));
                                               ((try
                                                     have :=
                                                       apspMacro_79703_2 apspMacro_79703_0 (by omega)));
                                               (revert apspMacro_79703_2)));
                                         (intros);
                                         (try simp only [Function.update_apply, Light.wrote] at *)));
                                     (omega))
                                 |
                                   ((simp [lp] at apspMacro_79703_1);
                                     (((repeat
                                             (((with_reducible
                                                     rename Light.SameOn _ _ _ => apspMacro_79703_3));
                                               ((try
                                                     have :=
                                                       apspMacro_79703_3 apspMacro_79703_0 (by omega)));
                                               (revert apspMacro_79703_3)));
                                         (intros);
                                         (try simp only [Function.update_apply, Light.wrote] at *)));
                                     (omega))
                                 |
                                   ((((repeat
                                             (((with_reducible
                                                     rename Light.SameOn _ _ _ => apspMacro_79703_4));
                                               ((try
                                                     have :=
                                                       apspMacro_79703_4 apspMacro_79703_0 (by omega)));
                                               (revert apspMacro_79703_4)));
                                         (intros);
                                         (try simp only [Function.update_apply, Light.wrote] at *)));
                                     (fail
                                         "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                   SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                   its condition K x does not follow from the hypotheses.")))))))
      p10 := sP10
      same := fun x hx => ?_ }
  rw [fP10 x (by omega), fP7 x (by omega), fP4 x (by omega), fP3 x (by omega)]

/-- The entry of pow, for a table of the powers b^0, …, b^L of a base b ≤ 10. -/
theorem SharedCallees.powTable {c : ℕ} (C : SharedCallees lim P c) {p : Par}
    (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word) (b dst : ℕ) (μ : ℕ → ℤ)
    (one_le : 1 ≤ b := by omega) (le_ten : b ≤ 10 := by omega) (dst_pos : 1 ≤ dst := by omega)
    (dst_le : dst + (p.L + 1) ≤ lim.space := by omega) :
    ∀ d, d ≤ lim.depth → Meets lim P pPow d [b, p.L, dst] μ (c * (p.L + 1)) fun _ μ' =>
      Seg μ' dst (powList b (p.L + 1)) ∧ SameOutside μ μ' dst (p.L + 1) :=
  C.pow b p.L dst μ dst_pos dst_le one_le
    (le_trans (by exact_mod_cast Nat.pow_le_pow_left le_ten _) h10)

/-- **The first part of shared.** -/
theorem sharedA_spec (std : Std lim) {c : ℕ} (C : SharedCallees lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) :
    Ends lim P d sharedA ⟨frame (sharedLoc0 p aX aY b0), μ⟩ (sharedTimeA c p) fun σ' =>
      (∃ r, σ'.loc = frame (sharedLocA p aX aY b0 r)) ∧ SharedA p b0 μ σ'.mem := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  have hsizes := p.sizes hmL
  have hTw := Par.ten_T_le h10
  unfold sharedA sharedTimeA sharedLoc0
  -- the addresses of the first eight areas
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.aP3 b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.aP4 b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.aP7 b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.aP10 b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.aPAS b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.aPHI b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.aPSI b0 : ℕ) ?_ ?_ ?_);
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
          (p.aMASK b0 : ℕ)
            -- the powers of 3, 4, 7 and 10
            
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
  -- the powers of 3, 4, 7 and 10
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
          Light.Ends.callToThen ((C.powTable h10 3 (p.aP3 b0) μ) _ (by omega)) ?_
            ?_ ?_ ?_
      | refine Light.Ends.callToThen (C.powTable h10 3 (p.aP3 b0) μ) ?_ ?_ ?_ ?_);
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
        ((rintro rP3 μP3 ⟨sP3, fP3⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
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
          Light.Ends.callToThen ((C.powTable h10 4 (p.aP4 b0) μP3) _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (C.powTable h10 4 (p.aP4 b0) μP3) ?_ ?_ ?_ ?_);
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
        ((rintro rP4 μP4 ⟨sP4, fP4⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
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
          Light.Ends.callToThen ((C.powTable h10 7 (p.aP7 b0) μP4) _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (C.powTable h10 7 (p.aP7 b0) μP4) ?_ ?_ ?_ ?_);
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
        ((rintro rP7 μP7 ⟨sP7, fP7⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
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
          Light.Ends.callToThen ((C.powTable h10 10 (p.aP10 b0) μP7) _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (C.powTable h10 10 (p.aP10 b0) μP7) ?_ ?_ ?_ ?_);
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
        ((rintro rP10 μP10 ⟨sP10, fP10⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hA := SharedA.of_calls sP3 fP3 sP4 fP4 sP7 fP7 sP10 fP10
  -- L - m, and then N₀ = 3^{L-m}, 10^L and 7^L from the tables
  have read : ∀ {b a i : ℕ}, Seg μP10 a (powList b (p.L + 1)) → i ≤ p.L →
      μP10 (a + i) = (b ^ i : ℕ) :=
    fun h hi => by rw [h.get (by rw [length_powList]; omega), getElem_powList]
  have hN0 : μP10 (p.aP3 b0 + p.Lo) = (p.N0 : ℕ) := read hA.p3 (by omega)
  have hT : μP10 (p.aP10 b0 + p.L) = (p.T : ℕ) := read hA.p10 le_rfl
  have hS7 : μP10 (p.aP7 b0 + p.L) = (p.S7 : ℕ) := read hA.p7 le_rfl
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.Lo : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.N0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hN0]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hN0] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hN0] <;> omega)));
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
    (refine Light.Ends.setToThen (p.T : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hT]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hT] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hT] <;> omega)));
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
    (refine Light.Ends.setToThen (p.S7 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hS7]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hS7] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hS7] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  exact ⟨⟨rP10, rfl⟩, hA⟩

/-- What the six calls of the second part that write to the memory leave in it (the square root
writes nothing): each writes its own area, above the areas of the calls before it, so that all the
tables are there at the end. -/
theorem SharedB.of_calls {p : Par} {b0 : ℕ} {μ μPas μPhi μMask μBand μDig3 μDig4 : ℕ → ℤ}
    (fPas : SameOutside μ μPas (p.aPAS b0) (p.L + 2))
    (sphi : Seg μPhi (p.aPHI b0) Spec.phiFlat)
    (spsi : Seg μPhi (p.aPHI b0 + 70) Spec.psiFlat)
    (fPhi : SameOutside μPas μPhi (p.aPHI b0) 140)
    (smask : ∀ s < p.KK, SegB μMask (p.aMASK b0 + s * p.L) (Spec.unrank p.L p.m s))
    (fMask : SameOutside μPhi μMask (p.aMASK b0) (p.KK * p.L))
    (sband : ∀ I < p.N, μBand (p.aBAND b0 + I) = (I / (p.K0 * p.N0) : ℕ)
      ∧ μBand (p.aBAND b0 + p.N + I) = (I / p.N0 % p.K0 : ℕ))
    (fBand : SameOutside μMask μBand (p.aBAND b0) (2 * p.N))
    (sdig3 : ∀ I < p.N, SegN μDig3 (p.aDIG3 b0 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % 3 ^
        p.Lo)))
    (fDig3 : SameOutside μBand μDig3 (p.aDIG3 b0) (p.N * p.Lo))
    (sdig4 : ∀ x < p.D, SegN μDig4 (p.aDIG4 b0 + x * p.m) (ThreeSumApsp.digitList 4 p.m (x % 4 ^
        p.m)))
    (fDig4 : SameOutside μDig3 μDig4 (p.aDIG4 b0) (p.D * p.m)) : SharedB p b0 μ μDig4 := by
  have hplaces := p.places b0
  have lphi := Spec.length_phiFlat
  have lpsi := Spec.length_psiFlat
  -- The last memory agrees with each earlier one below the area that was written next.
  have lowDig3 : ∀ x < p.aDIG4 b0, μDig4 x = μDig3 x := fun x hx => fDig4 x (Or.inl hx)
  have lowBand : ∀ x < p.aDIG3 b0, μDig4 x = μBand x := fun x hx => by
    rw [lowDig3 x (by omega), fDig3 x (Or.inl hx)]
  have lowMask : ∀ x < p.aBAND b0, μDig4 x = μMask x := fun x hx => by
    rw [lowBand x (by omega), fBand x (Or.inl hx)]
  have lowPhi : ∀ x < p.aMASK b0, μDig4 x = μPhi x := fun x hx => by
    rw [lowMask x (by omega), fMask x (Or.inl hx)]
  refine
    { phi := sphi.congr fun i hi => lowPhi _ (by omega)
      psi := spsi.congr fun i hi => lowPhi _ (by omega)
      mask := fun s hs => (smask s hs).congr fun i hi => lowMask _ ?_
      band := fun I hI => (lowBand _ (by omega)).trans (sband I hI).1
      block := fun I hI => (lowBand _ (by omega)).trans (sband I hI).2
      dig3 := fun I hI => (sdig3 I hI).congr fun i hi => lowDig3 _ ?_
      dig4 := fun x hx => ?_
      same := fun x hx => ?_ }
  · rw [List.length_map, Spec.length_unrank] at hi
    have := Nat.mul_add_lt_mul hs hi
    omega
  · have hi' : i < p.Lo := by simpa [ThreeSumApsp.digitList] using hi
    have := Nat.mul_add_lt_mul hI hi'
    omega
  · have h := sdig4 x hx
    rwa [Nat.mod_eq_of_lt (show x < 4 ^ p.m from hx)] at h
  · show μDig4 x = μ x
    rw [fDig4 x (by omega), fDig3 x (by omega), fBand x (by omega), fMask x (by omega),
      fPhi x (by omega), fPas x (by omega)]

/-- **The second part of shared.** -/
theorem sharedB_spec (std : Std lim) {c : ℕ} (C : SharedCallees lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) (r0 : ℤ) :
    Ends lim P d sharedB ⟨frame (sharedLocA p aX aY b0 r0), μ⟩ (sharedTimeB c p) fun σ' =>
      (∃ r, σ'.loc = frame (sharedLocB p aX aY b0 r)) ∧ SharedB p b0 μ σ'.mem := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  have hsizes := p.sizes hmL
  have eKK : p.KK = p.K0 * p.K0 := rfl
  have hTw := Par.ten_T_le h10
  unfold sharedB sharedTimeB sharedLocA
  -- K := binom(L, m)
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
            ((C.binom p.L p.m (p.aPAS b0) μ (by omega) hmL
                (le_trans (by exact_mod_cast p.two_pow_le_T)
                  (by omega : (p.T : ℤ) ≤ lim.word)))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.binom p.L p.m (p.aPAS b0) μ (by omega) hmL
              (le_trans (by exact_mod_cast p.two_pow_le_T)
                (by omega : (p.T : ℤ) ≤ lim.word)))
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
        ((rintro r μPas ⟨hr, fPas⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  obtain rfl : r = (p.K : ℕ) := hr
  -- K₀ := ⌊√K⌋ and K₀²
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
            ((C.sqrt p.K μPas (by (push_cast); (omega))) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (C.sqrt p.K μPas (by (push_cast); (omega))) ?_ ?_
            ?_ ?_);
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
        ((rintro r μPas' ⟨hr, hμ⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  obtain rfl : r = (p.K0 : ℕ) := hr
  obtain rfl : μPas = μPas' := hμ.symm
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
          (p.KK : ℕ)
            -- the coefficients and the table of subsets
            
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
  -- the coefficients and the table of subsets
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
            ((C.coef (p.aPHI b0) μPas (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (C.coef (p.aPHI b0) μPas (by omega)) ?_ ?_ ?_ ?_);
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
        ((rintro rPhi μPhi ⟨sphi, spsi, fPhi⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
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
            ((C.subsets p.L p.m p.KK (p.aMASK b0) μPhi (by omega) hmL p.KK_le_K
                (by (push_cast); (omega)))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.subsets p.L p.m p.KK (p.aMASK b0) μPhi (by omega) hmL p.KK_le_K
              (by (push_cast); (omega)))
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
        ((rintro rMask μMask
              ⟨smask, fMask⟩
                  -- band and block of every row
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- band and block of every row
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.aBAND b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.aBLOCK b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.aDIG3 b0 : ℕ) ?_ ?_ ?_);
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
    (first
      |
        refine
          Light.Ends.callToThen
            ((C.counters p.N p.K0 p.N0 (p.aBAND b0) μMask (by omega) (by omega)
                (by omega) (by (push_cast); (omega)))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.counters p.N p.K0 p.N0 (p.aBAND b0) μMask (by omega) (by omega)
              (by omega) (by (push_cast); (omega)))
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
        ((rintro rBand μBand
              ⟨sband, fBand⟩
                  -- the digits of every row and of every column
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the digits of every row and of every column
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
            ((C.digits p.N 3 p.Lo (p.aDIG3 b0) μBand (by omega) (by norm_num)
                (by (push_cast); (omega)) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.digits p.N 3 p.Lo (p.aDIG3 b0) μBand (by omega) (by norm_num)
              (by (push_cast); (omega)) (by omega))
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
        ((rintro rDig3 μDig3 ⟨sdig3, fDig3⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.aDIG4 b0 : ℕ) ?_ ?_ ?_);
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
    (first
      |
        refine
          Light.Ends.callToThen
            ((C.digits p.D 4 p.m (p.aDIG4 b0) μDig3 (by omega) (by norm_num)
                (by (push_cast); (omega)) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.digits p.D 4 p.m (p.aDIG4 b0) μDig3 (by omega) (by norm_num)
              (by (push_cast); (omega)) (by omega))
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
        ((rintro rDig4 μDig4 ⟨sdig4, fDig4⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.aENCA b0 : ℕ) ?_ ?_ ?_);
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
  exact ⟨⟨rDig4, rfl⟩,
    .of_calls fPas sphi spsi fPhi smask fMask sband fBand sdig3 fDig3 sdig4 fDig4⟩

/-- What bandArray reads of the tables. -/
theorem SharedTables.bandTables {p : Par} {b0 : ℕ} {μ : ℕ → ℤ} (h : SharedTables p b0 μ) :
    BandTables p μ (p.aMASK b0) (p.aDIG3 b0) (p.aDIG4 b0) (p.aENCA b0) := by
  have hplaces := p.places b0
  exact ⟨h.mask, h.dig3, h.dig4, by omega, by omega, by omega⟩














/-- What encodeBands assumes holds once the tables are there, for either of the two areas enc of
encodings. -/
theorem SharedTables.bandsPre {p : Par} {b0 tab enc : ℕ} {μ : ℕ → ℤ} {coefs : List ℤ} {V : ℤ}
    (h : SharedTables p b0 μ) (hsp : p.sharedEnd b0 ≤ lim.space) (hV0 : 0 ≤ V)
    (hVB : 7 ^ (p.L + 1) * V ≤ lim.word) (coef : Seg μ tab coefs) (coef_le : tab + 70 ≤ enc)
    (le_enc : p.aENCA b0 ≤ enc) (enc_le : enc + p.nB * p.T ≤ p.aARR b0) :
    BandsPre lim p μ (p.bandsArgs b0 tab enc) coefs V := by
  have hplaces := p.places b0
  exact
    { tables := h.bandTables.mono le_enc
      coef := coef
      coef_le := coef_le
      p7 := h.p7
      p7_le := show p.aP7 b0 + (p.L + 1) ≤ enc by omega
      p10 := h.p10
      p10_le := show p.aP10 b0 + (p.L + 1) ≤ enc by omega
      enc_le := enc_le
      arr_le := show p.aARR b0 + p.S7 ≤ p.aZS b0 by omega
      zs_le := show p.aZS b0 + p.S7 ≤ lim.space by omega
      V_nonneg := hV0
      word := hVB }

/-- The number of bands, from the band of the last row. -/
theorem nB_eq (p : Par) (hmL : p.m ≤ p.L) :
    (p.N = 0 → p.nB = 0) ∧ (0 < p.N → p.nB = (p.N - 1) / (p.K0 * p.N0) + 1) := by
  have hb : 0 < p.K0 * p.N0 := Nat.mul_pos (K0_pos hmL) (N0_pos _ _)
  have e : p.nB = (p.N + p.K0 * p.N0 - 1) / (p.K0 * p.N0) := rfl
  constructor
  · intro h
    rw [e, h, Nat.zero_add]
    exact Nat.div_eq_of_lt (by omega)
  · intro h
    rw [e, ← Nat.add_div_right _ hb]
    congr 1
    omega

/-- **The number of bands**: 0 if there is no row, and else one more than the band of the last
row. -/
theorem sharedBands_spec (std : Std lim) {d : ℕ} {p : Par} (hmL : p.m ≤ p.L) {aX aY b0 : ℕ}
    (hsp : p.sharedEnd b0 ≤ lim.space) (μ : ℕ → ℤ) (r0 : ℤ) (tb : SharedTables p b0 μ) :
    Ends lim P d sharedBands ⟨frame (sharedLocB p aX aY b0 r0), μ⟩ 13 fun σ' =>
      σ' = ⟨frame (setLocal (sharedLocB p aX aY b0 r0) Bands (p.nB : ℕ)), μ⟩ := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  obtain ⟨hnB0, hnB1⟩ := nB_eq p hmL
  unfold sharedBands sharedLocB
  refine Ends.iteLast (fun hN => ?_) (fun hN => ?_)
  · -- nB := 0
    have hNzero : p.N = 0 := by simpa using hN
    exact Ends.setTo (p.nB : ℕ) rfl (by simp [hnB0 hNzero]; omega)
  · -- nB := mem[BAND + (N - 1)] + 1
    have hNpos : 0 < p.N := Nat.pos_of_ne_zero (by simpa using hN)
    have hlast := tb.band (p.N - 1) (by omega)
    have haddr : ((p.aBAND b0 : ℤ) + ((p.N : ℤ) - 1)).toNat = p.aBAND b0 + (p.N - 1) := by omega
    have hle : (p.N - 1) / (p.K0 * p.N0) ≤ p.N := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    have hnB := hnB1 hNpos
    generalize (p.N - 1) / (p.K0 * p.N0) = q at hlast hle hnB
    exact Ends.setTo (p.nB : ℕ) rfl (by (((try have := Light.Std.space_le (by assumption)));
                                            ((try have := Light.Std.const_le (by assumption)));
                                            (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hlast, hnB] <;> omega)))

/-- What the two calls of encodeBands and the stores of the directory leave in the memory. -/
theorem SharedReady.of_calls {p : Par} (hmL : p.m ≤ p.L) {aX aY b0 : ℕ}
    {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μEncA μEncB μDir : ℕ → ℤ}
    (tb : SharedTables p b0 μ)
    (sA : ∀ β < p.nB, Seg μEncA (p.aENCA b0 + β * p.T)
      (Spec.arrT (encodingL (bandArrayL (Spec.stdLayout hmL) X β))))
    (fEncA : SameOutside μ μEncA (p.aENCA b0) (p.sharedEnd b0 - p.aENCA b0))
    (sB : ∀ β < p.nB, Seg μEncB (p.aENCB b0 + β * p.T)
      (Spec.arrT (encodingR (bandArrayR (Spec.stdLayout hmL) Y β))))
    (fEncB : SameOutside μEncA μEncB (p.aENCB b0) (p.sharedEnd b0 - p.aENCB b0))
    (sdir : SegN μDir b0 (dirList p aX aY b0)) (fDir : SameOutside μEncB μDir b0 31) :
    SharedReady p hmL aX aY b0 X Y μDir ∧ SameOutside μ μDir b0 (p.sharedEnd b0 - b0) := by
  have hplaces := p.places b0
  have above : ∀ x, p.aP3 b0 ≤ x → μDir x = μEncB x := fun x hx => fDir x (Or.inr (by omega))
  have tbDir : SharedTables p b0 μDir := tb.congr fun x h1 h2 => by
    rw [above x h1, fEncB x (Or.inl (by omega)), fEncA x (Or.inl h2)]
  refine ⟨{ tbDir with
    dir := sdir
    encA := fun β hβ => (sA β hβ).congr fun i hi => ?_
    encB := fun β hβ => (sB β hβ).congr fun i hi => above _ (by omega) }, fun x hx => ?_⟩
  · rw [Spec.length_arrT] at hi
    have := Nat.mul_add_lt_mul hβ (show i < p.T from hi)
    rw [above _ (by omega), fEncB _ (Or.inl (by omega))]
  · show μDir x = μ x
    rw [fDir x (by omega), fEncB x (by omega), fEncA x (by omega)]

/-- **The third part of shared.** -/
theorem sharedC_spec (std : Std lim) {c : ℕ} (C : SharedCallees lim P c) {d : ℕ} {p : Par}
    (hmL : p.m ≤ p.L) {aX aY b0 : ℕ} (hd : d + (p.L + 3) ≤ lim.depth)
    (hsp : p.sharedEnd b0 ≤ lim.space) (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word)
    (μ : ℕ → ℤ) (r0 : ℤ) {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
    {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {V : ℤ} (hX : MatAt μ aX X)
    (hY : MatAt μ aY Y) (hXle : aX + p.N * p.D ≤ b0) (hYle : aY + p.D * p.N ≤ b0) (hV0 : 0 ≤ V)
    (hVX : ∀ i j, |X i j| ≤ V) (hVY : ∀ i j, |Y i j| ≤ V) (hVB : 7 ^ (p.L + 1) * V ≤ lim.word)
    (tb : SharedTables p b0 μ) :
    Ends lim P d sharedC ⟨frame (sharedLocB p aX aY b0 r0), μ⟩ (sharedTimeC c p) fun σ' =>
      SharedReady p hmL aX aY b0 X Y σ'.mem ∧ SameOutside μ σ'.mem b0 (p.sharedEnd b0 - b0) := by
  have hw := std.space_le
  have h100 := std.const_le
  have hplaces := p.places b0
  have hsizes := p.sizes hmL
  have hTw := Par.ten_T_le h10
  unfold sharedC sharedTimeC
  -- the number of bands
  refine Ends.next 13 ((sharedBands_spec std hmL hsp μ r0 tb).mono le_rfl ?_)
  rintro _ rfl
  unfold sharedLocB
  -- the last four addresses
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.aENCB b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.aARR b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (p.aZS b0 : ℕ) ?_ ?_ ?_);
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
          (p.sharedEnd b0 : ℕ)
            -- the encodings of the row bands of X
            
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
  -- the encodings of the row bands of X
  have preA : BandsPre lim p μ (p.bandsArgs b0 (p.aPHI b0) (p.aENCA b0)) Spec.phiFlat V :=
    tb.bandsPre hsp hV0 hVB tb.phi (coef_le := by omega) (le_enc := le_rfl) (enc_le := by omega)
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
            ((C.bandsL p hmL _ aX μ X V preA hX
                (hXle.trans (show b0 ≤ p.aENCA b0 by omega)) hVX)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.bandsL p hmL _ aX μ X V preA hX
              (hXle.trans (show b0 ≤ p.aENCA b0 by omega)) hVX)
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
        ((rintro rEncA μEncA
              ⟨sA, fEncA⟩
                  -- the encodings of the column bands of Y
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the encodings of the column bands of Y
  have lowEncA : ∀ x < p.aENCA b0, μEncA x = μ x := fun x hx => fEncA x (Or.inl hx)
  have tbEncA : SharedTables p b0 μEncA := tb.congr fun x _ hx => lowEncA x hx
  have hYle' : aY + ThreeSumApsp.D p.m * p.N ≤ p.aENCA b0 := le_trans hYle (by omega)
  have preB : BandsPre lim p μEncA (p.bandsArgs b0 (p.aPSI b0) (p.aENCB b0)) Spec.psiFlat V :=
    tbEncA.bandsPre hsp hV0 hVB tbEncA.psi (coef_le := by omega) (le_enc := by omega)
      (enc_le := by omega)
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
            ((C.bandsR p hmL _ aY μEncA Y V preB (hY.congr_below lowEncA hYle')
                (hYle.trans (show b0 ≤ p.aENCB b0 by omega)) hVY)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.bandsR p hmL _ aY μEncA Y V preB (hY.congr_below lowEncA hYle')
              (hYle.trans (show b0 ≤ p.aENCB b0 by omega)) hVY)
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
        ((rintro rEncB μEncB
              ⟨sB, fEncB⟩
                  -- the directory
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the directory
  refine (storeLocals_spec hw (base := b0) _ (by simp) _ 0 μEncB (by simp; omega)).mono
    (by simp; omega) ?_
  rintro ⟨_, μDir⟩ ⟨sdir, fDir⟩
  exact SharedReady.of_calls hmL tb sA fEncA sB fEncB (by simpa [SegN, dirList] using sdir)
    (by simpa using fDir)

/-- The time of the shared stage has the shape of its entry. -/
theorem sharedTime_le (c : ℕ) (p : Par) :
    sharedTimeA c p + (sharedTimeB c p + sharedTimeC c p) ≤ (12 * c + 600) * sharedShape p := by
  unfold sharedTimeA sharedTimeB sharedTimeC sharedShape
  -- The terms that are not in the shape: L + 1 ≤ (L + 1)², N + 1 ≤ (N + 1) (L - m + 1), 1 ≤ (L +
  -- 1)².
  have hL : p.L + 1 ≤ (p.L + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN : p.N + 1 ≤ (p.N + 1) * (p.Lo + 1) := Nat.le_mul_of_pos_right _ (by omega)
  generalize (p.L + 1) ^ 2 = s, Nat.sqrt p.K + 1 = q, (p.KK + 1) * (p.L + 1) = u,
    (p.N + 1) * (p.Lo + 1) = w, (p.D + 1) * (p.m + 1) = x,
    p.nB * (p.T + bandArrayShape p) = y at hL hN ⊢
  have hcL := Nat.mul_le_mul_left c hL
  have hcN := Nat.mul_le_mul_left c hN
  have hc1 := Nat.mul_le_mul_left c (show 1 ≤ s by omega)
  have hy : c * (y + 1) = c * y + c := Nat.mul_succ c y
  have hright : (12 * c + 600) * (s + q + u + w + x + y) = 12 * (c * s) + 12 * (c * q)
      + 12 * (c * u) + 12 * (c * w) + 12 * (c * x) + 12 * (c * y)
      + 600 * (s + q + u + w + x + y) := by ring
  omega

/-- The tables of the first part are still there after the second part. -/
theorem SharedTables.of_parts {p : Par} {b0 : ℕ} {μ μA μB : ℕ → ℤ} (hA : SharedA p b0 μ μA)
    (hB : SharedB p b0 μA μB) : SharedTables p b0 μB := by
  have hplaces := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  exact
    { hB.toRowTables with
      p3 := hA.p3.keep (by ((try have := hB.same); (try have := lp);
                             (((try refine Light.SameOn.cell ?_);
                                 (intro apspMacro_96898_0 apspMacro_96898_1);
                                 (first
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_96898_2));
                                                 ((try
                                                       have :=
                                                         apspMacro_96898_2 apspMacro_96898_0 (by omega)));
                                                 (revert apspMacro_96898_2)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((simp [hB.same, lp] at apspMacro_96898_1);
                                       (((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_96898_3));
                                                 ((try
                                                       have :=
                                                         apspMacro_96898_3 apspMacro_96898_0 (by omega)));
                                                 (revert apspMacro_96898_3)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_96898_4));
                                                 ((try
                                                       have :=
                                                         apspMacro_96898_4 apspMacro_96898_0 (by omega)));
                                                 (revert apspMacro_96898_4)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (fail
                                           "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                     SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                     its condition K x does not follow from the hypotheses.")))))))
      p4 := hA.p4.keep (by ((try have := hB.same); (try have := lp);
                             (((try refine Light.SameOn.cell ?_);
                                 (intro apspMacro_96951_0 apspMacro_96951_1);
                                 (first
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_96951_2));
                                                 ((try
                                                       have :=
                                                         apspMacro_96951_2 apspMacro_96951_0 (by omega)));
                                                 (revert apspMacro_96951_2)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((simp [hB.same, lp] at apspMacro_96951_1);
                                       (((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_96951_3));
                                                 ((try
                                                       have :=
                                                         apspMacro_96951_3 apspMacro_96951_0 (by omega)));
                                                 (revert apspMacro_96951_3)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_96951_4));
                                                 ((try
                                                       have :=
                                                         apspMacro_96951_4 apspMacro_96951_0 (by omega)));
                                                 (revert apspMacro_96951_4)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (fail
                                           "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                     SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                     its condition K x does not follow from the hypotheses.")))))))
      p7 := hA.p7.keep (by ((try have := hB.same); (try have := lp);
                             (((try refine Light.SameOn.cell ?_);
                                 (intro apspMacro_97004_0 apspMacro_97004_1);
                                 (first
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_97004_2));
                                                 ((try
                                                       have :=
                                                         apspMacro_97004_2 apspMacro_97004_0 (by omega)));
                                                 (revert apspMacro_97004_2)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((simp [hB.same, lp] at apspMacro_97004_1);
                                       (((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_97004_3));
                                                 ((try
                                                       have :=
                                                         apspMacro_97004_3 apspMacro_97004_0 (by omega)));
                                                 (revert apspMacro_97004_3)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_97004_4));
                                                 ((try
                                                       have :=
                                                         apspMacro_97004_4 apspMacro_97004_0 (by omega)));
                                                 (revert apspMacro_97004_4)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (fail
                                           "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                     SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                     its condition K x does not follow from the hypotheses.")))))))
      p10 := hA.p10.keep (by ((try have := hB.same); (try have := lp);
                               (((try refine Light.SameOn.cell ?_);
                                   (intro apspMacro_97059_0 apspMacro_97059_1);
                                   (first
                                     |
                                       ((((repeat
                                                 (((with_reducible
                                                         rename Light.SameOn _ _ _ => apspMacro_97059_2));
                                                   ((try
                                                         have :=
                                                           apspMacro_97059_2 apspMacro_97059_0 (by omega)));
                                                   (revert apspMacro_97059_2)));
                                             (intros);
                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                         (omega))
                                     |
                                       ((simp [hB.same, lp] at apspMacro_97059_1);
                                         (((repeat
                                                 (((with_reducible
                                                         rename Light.SameOn _ _ _ => apspMacro_97059_3));
                                                   ((try
                                                         have :=
                                                           apspMacro_97059_3 apspMacro_97059_0 (by omega)));
                                                   (revert apspMacro_97059_3)));
                                             (intros);
                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                         (omega))
                                     |
                                       ((((repeat
                                                 (((with_reducible
                                                         rename Light.SameOn _ _ _ => apspMacro_97059_4));
                                                   ((try
                                                         have :=
                                                           apspMacro_97059_4 apspMacro_97059_0 (by omega)));
                                                   (revert apspMacro_97059_4)));
                                             (intros);
                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                         (fail
                                             "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                       its condition K x does not follow from the hypotheses."))))))) }

/-- **shared** meets its entry of the map: if every callee meets its entry with the constant c, then
shared does with the constant 12 c + 600. -/
theorem shared_entry (std : Std lim) (hP : P[pShared]? = some sharedBody) {c : ℕ}
    (C : SharedCallees lim P c) {c' : ℕ} (hc : 12 * c + 600 ≤ c') : SharedSpec lim P c' := by
  intro p hmL aX aY b0 μ X Y V pre d hd
  have hplaces := p.places b0
  refine .mono_const (.of_body hP (Ends.mono ?_ (sharedTime_le c p) fun _ h => h)) hc
  rw [← frame_append_zeros [(p.L : ℤ), p.m, p.N, p.D, aX, aY, b0] 26]
  unfold sharedBody
  -- the first part
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen (sharedA_spec std C hmL hd pre.space pre.ten μ) ?_
            ?_
      |
        refine
          Light.Ends.pieceLast (sharedA_spec std C hmL hd pre.space pre.ten μ) ?_
            ?_);
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
    (on_goal -1 => rintro ⟨locA, μA⟩ ⟨⟨rA, hlocA⟩, hA⟩)
  obtain rfl : locA = _ := hlocA
  dsimp only at hA
  -- the second part
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen (sharedB_spec std C hmL hd pre.space pre.ten μA rA)
            ?_ ?_
      |
        refine
          Light.Ends.pieceLast (sharedB_spec std C hmL hd pre.space pre.ten μA rA)
            ?_ ?_);
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
    (on_goal -1 => rintro ⟨locB, μB⟩ ⟨⟨rB, hlocB⟩, hB⟩)
  obtain rfl : locB = _ := hlocB
  dsimp only at hB
  -- the third part; the matrices lie below the block, and max V 0 bounds their entries as well
  have low : ∀ x < b0, μB x = μ x := fun x hx => by
    rw [hB.same x (Or.inl (by omega)), hA.same x (Or.inl (by omega))]
  have hVB' : 7 ^ (p.L + 1) * max V 0 ≤ lim.word := by
    rcases le_total V 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact le_trans (by norm_num) std.const_le
    · rw [max_eq_left h]
      exact pre.seven
  refine (sharedC_spec std C hmL hd pre.space pre.ten μB rB (pre.matX.congr_below low pre.belowX)
    (pre.matY.congr_below low pre.belowY) pre.belowX pre.belowY (le_max_right V 0)
    (fun i j => (pre.absX i j).trans (le_max_left _ _))
    (fun i j => (pre.absY i j).trans (le_max_left _ _)) hVB' (.of_parts hA hB)).mono (by omega) ?_
  rintro σ' ⟨hR, hf⟩
  exact ⟨hR, fun x hx => by rw [hf x hx, hB.same x (by omega), hA.same x (by omega)]⟩

end Light.Sec2

end
end

section


/-!
# Theorem 5: the program

The list of the procedures of Theorem 5's program, in the order of their numbers.  An entry is the
specification of a procedure together with a bound on its time, a constant times a shape.  In every
program that begins with this list, the procedures that the shared stage calls meet their entries
with the constant cShared5 (sharedCallees_of_prefix), and those that the solver calls with the
constant cMain5 (mainCallees_of_prefix).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.WordRam











/-- A procedure of program5 is a procedure, with the same number, of every program that begins with
program5. -/
theorem at_prefix {p : ℕ} {body : Stmt} (h : program5[p]? = some body) (R : Program) :
    (program5 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R

/-! ## All entries -/



































end Light.Sec2

end
end

section


/-!
# Corollaries 26 and 31 in the light language: procedure numbers, time functions and interfaces

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D with
zero columns of X and zero rows of Y." Proof of Corollary 31: "We repeat the proof of Corollary 26
with L := ⌈cm⌉ and t := ⌈θm⌉"; "for smaller m the corollary again holds trivially". Here a query
then computes an inner product, which takes a bounded number of steps since D is bounded.

The routines are relocatable: they receive the addresses of X and Y and a free pointer fr. From fr
on they use

    flag (1) | b0 (1) | 4^m (1) | X' (N 4^m) | Y' (4^m N) | the block of Theorem 30 from b0 on

flag = 1 says that the data structure of Theorem 30 has been built for the padded matrices X', Y';
flag = 0 that m is below the threshold m₀ (a constant of the program text) and that queries compute
inner products. Nothing is assumed about the cells from fr on.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace Proc















end Proc

/-! ## Time functions -/








/-! ## The small routines -/








































/-! ### copy and fill are those of the library -/

theorem copy_ok {lim : Limits} {P : Program} (hP : P[Proc.copy]? = some copyBody)
    (hstd : Std lim) : CopySpec lim P := by
  intro src dst n μ h1 h2 _ h4 d _
  exact copy_meets hP hstd.space_le h1 h2 h4

theorem fill_ok {lim : Limits} {P : Program} (hP : P[Proc.fill]? = some fillBody)
    (hstd : Std lim) : FillSpec lim P := by
  intro dst n x μ h1 _ d _
  refine (fill_meets hP hstd.space_le h1).mono le_rfl fun _ μ' h => ⟨fun i hi => ?_, h.2⟩
  have := h.1 i (by simpa using hi)
  simpa using this

/-! ### ⌈log₄ D⌉ -/

namespace Log4








end Log4








theorem log4_meets {lim : Limits} {P : Program} (hP : P[Proc.log4]? = some log4Body)
    (hstd : Std lim) : Log4Spec lim P := by
  intro D₀ a μ ha hw hmw
  refine fun d _ => ⟨log4Body, hP, ?_⟩
  have h100 := hstd.const_le
  obtain ⟨F, hF⟩ : ∃ F, F = 4 ^ Nat.clog 4 D₀ := ⟨_, rfl⟩
  have hge : D₀ ≤ F := hF ▸ Nat.le_pow_clog (by norm_num) D₀
  rw [← hF] at hw ⊢
  unfold log4Body tLog4
  -- pow := 1 ; exp := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 1 ?_ ?_ ?_);
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
          0
            -- while pow < D: pow := pow * 4 ; exp := exp + 1.  Before round i, pow = 4^i and exp = i.
            
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
  -- while pow < D: pow := pow * 4 ; exp := exp + 1.  Before round i, pow = 4^i and exp = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [D₀, a, ((4 ^ i : ℕ) : ℤ), i], μ⟩)
    (Nat.clog 4 D₀) rfl ?round ?done (hT := le_rfl))
  case round =>
    rintro i _ hi rfl
    have hlt := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 hi
    have hpow : 4 ^ i * 4 ≤ F := by
      rw [hF, ← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) hi
    rw [pow_succ]
    generalize 4 ^ i = p at hlt hpow ⊢
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, by (((try have := Light.Std.space_le (by assumption)));
                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    rw [← hF]
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, ?_⟩
    -- mem[a] := pow ; return exp
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen a F ?_ ?_ ?_);
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
      (refine Light.Ends.setToThen (Nat.clog 4 D₀ : ℤ) ?_ ?_ ?_);
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
    exact ⟨rfl, rfl⟩

end Light.Sec4

end
end

section


/-!
# Theorem 30 in the light language: the memory map and the invariant of the data structure

The data structure occupies one block of the memory, from a base address b0 on. First comes the
shared block of Section 2 (directory, tables, the encodings of all bands), and behind it the areas
of Section 4:

    WD (L) | CUR (L) | BOX (L) | SS (m) | FP (1) | ROOTS (nB²) | TR (cap)

WD holds the digits of the output string of a query; CUR, BOX and SS are scratch strings; FP holds
the length of the trie array; ROOTS holds the roots of the tries, that of tile (β, β') in the cell
β nB + β'; TR is the trie area. Cell 31 of the directory holds t. `Areas` says where the tables that
the routines of Section 4 read and the areas of Section 4 lie, and `areas` proves it.

Two routines know this map: preCore(L, m, t, N, D, aX, aY, b0) builds the block from the matrices at
aX and aY, which lie below b0, and queryAt(I, J, b0) answers a query from it. They are relocatable,
so that Theorem 30, its offline form and Corollary 26 use the same two routines. The main procedures
of Theorem 30's programs only read the sizes from the input and compute the addresses. For Corollary
26 a routine of its own stands in between: it finds m and, from the threshold of the proof on, L and
t, writes padded copies of the matrices, and runs `preCore` on them.

Section 4.3: "Our data structure consists of three components: the list of the K₀² subsets Q
assigned to the block products of a tile […], the encodings of all row bands and all column bands,
and for every tile, the values of all its boxes". In the invariant DSReady the field shared holds
the first two, and the fields roots and trie hold the third: "for each tile we store its boxes, with
their values, in a standard trie on their strings of L symbols". The tries of all tiles lie in one
array (trie), and the table roots has the root of the trie of each tile. The invariant depends only
on the cells from b0 on, without the scratch strings (`DSReady.congr`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The map -/






















/-! ## Where the areas lie -/



















/-- The tables and the areas lie as Areas says. -/
theorem areas (p : Sec2.Par) (t b0 : ℕ) : Areas p t b0 := by
  have hplaces := p.places b0
  have hWD : aWD p b0 = p.sharedEnd b0 := rfl
  have hCUR : aCUR p b0 = aWD p b0 + p.L := rfl
  have hBOX : aBOX p b0 = aCUR p b0 + p.L := rfl
  have hSS : aSS p b0 = aBOX p b0 + p.L := rfl
  have hFP : aFP p b0 = aSS p b0 + p.m := rfl
  have hROOTS : aROOTS p b0 = aFP p b0 + 1 := rfl
  have hTR : aTR p b0 = aROOTS p b0 + p.nB * p.nB := rfl
  have hTOP : top p t b0 = aTR p b0 + trieCap p t + 1 := rfl
  constructor <;> omega










/-- The block holds more than its directory. -/
theorem base_add_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 + 32 < top p t b0 := by
  obtain ⟨⟩ := areas p t b0
  omega

/-- The block is not empty. -/
theorem base_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 < top p t b0 :=
  (Nat.le_add_right b0 32).trans_lt (base_add_lt_top p t b0)










/-! ## The directory -/

namespace Dir




















end Dir

/-! ## The invariant -/



























section

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- The invariant depends only on the cells from b0 on, without the scratch strings WD, CUR, BOX,
SS. -/
theorem DSReady.congr (h : DSReady p t hmL aX aY b0 X Y μ)
    (he : ∀ a, b0 ≤ a → Outside (aWD p b0) (3 * p.L + p.m) a → μ' a = μ a) :
    DSReady p t hmL aX aY b0 X Y μ' := by
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  exact ⟨h.shared.congr fun a ha hlt _ => he a ha (by omega),
    by rw [he _ (by omega) (by omega)]; exact h.cellT,
    h.roots.congr fun i _ => he _ (by omega) (by omega),
    h.trie.congr fun i _ => he _ (by omega) (by omega)⟩







/-- The invariant of the data structure only depends on the cells from b0 on. -/
theorem dsReady_congr (h : DSReady p t hmL aX aY b0 X Y μ) (he : ∀ a, b0 ≤ a → μ' a = μ a) :
    DSReady p t hmL aX aY b0 X Y μ' :=
  h.congr fun a ha _ => he a ha

end












/-! ## The two routines that know the map -/




































end Light.Sec4

end
end

section


/-!
# Ceilings of quotients and logarithms, floors and ceilings of roots

General facts about natural and real numbers. The quotient of two natural numbers, rounded up, is
Mathlib's `a ⌈/⌉ b`. It is computed by `Nat.ceilDiv_eq_add_pred_div : a ⌈/⌉ b = (a + b - 1) / b`.
It is the ceiling of the real quotient (`Nat.ceil_div_eq_ceilDiv`) and the least `k` with
`a ≤ k * b` (`Nat.ceilDiv_le_iff`, `Nat.lt_ceilDiv_iff`), so `a ≤ a ⌈/⌉ b * b < a + b`
(`Nat.le_ceilDiv_mul`, `Nat.ceilDiv_mul_lt`). The power of `b` with exponent `⌈log_b n⌉` is at most
`b * n` (`Nat.pow_clog_le_mul`). A natural number is compared with an `e`-th root by its `e`-th
power (`Real.natCast_le_rpow_inv_iff`, `Real.rpow_inv_le_natCast_iff`). `cbrtCeil n` is the cube
root of `n`, rounded up.
-/

public section

namespace Nat

/-! ## The ceiling of a quotient of natural numbers -/

/-- `a ⌈/⌉ b ≤ k` says that `k` pieces of size `b` cover `a`. Mathlib's `ceilDiv_le_iff_le_mul` has
`b * k` on the right. -/
theorem ceilDiv_le_iff {a b k : ℕ} (hb : 0 < b) : a ⌈/⌉ b ≤ k ↔ a ≤ k * b := by
  rw [ceilDiv_le_iff_le_mul hb, Nat.mul_comm]

/-- `i < a ⌈/⌉ b` says that `i` pieces of size `b` do not cover `a`. -/
theorem lt_ceilDiv_iff {a b i : ℕ} (hb : 0 < b) : i < a ⌈/⌉ b ↔ i * b < a := by
  rw [← Nat.not_le, ceilDiv_le_iff hb, Nat.not_le]





















/-! ## The ceiling of a logarithm

`Real.natCeil_logb_natCast : ⌈Real.logb b n⌉₊ = Nat.clog b n` passes from real to natural numbers,
and `Nat.le_pow_clog : 1 < b → x ≤ b ^ Nat.clog b x` is the lower bound. -/











end Nat

namespace Real

/-! ## Roots

The `e`-th root of `t` is written `(t : ℝ) ^ ((e : ℝ)⁻¹)`. With these two lemmas,
`Nat.le_floor_iff` and `Nat.ceil_le`, its floor and its ceiling are described by powers of natural
numbers. -/















end Real

namespace ThreeSumApsp




end ThreeSumApsp

end
end

section


/-!
# Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query

m = ⌈log₄ D⌉ (`logFour`), the places of the padded matrices and of the block of Theorem 30 behind
the free pointer (`paddedXAt`, `paddedYAt`, `blockAt`), the text of the query, and the bounds on the
entries of the padded matrices. The text of the query serves all rational parameters; its
specification is `QuerySpec31`, proved in `query31_meets`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters and map -/









/-! ## The query -/

namespace Query31










end Query31








theorem abs_padInnerCols_le {N D₀ D' : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {U : ℤ}
    (h : ∀ i j, |X i j| ≤ U) (hU : 0 ≤ U) (i : Fin N) (j : Fin D') :
    |padInnerCols D' X i j| ≤ U := by
  unfold padInnerCols
  split_ifs
  · exact h _ _
  · simpa using hU

theorem abs_padInnerRows_le {N D₀ D' : ℕ} {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ}
    (h : ∀ i j, |Y i j| ≤ U) (hU : 0 ≤ U) (i : Fin D') (j : Fin N) :
    |padInnerRows D' Y i j| ≤ U := by
  unfold padInnerRows
  split_ifs
  · exact h _ _
  · simpa using hU

theorem le_D_logFour (D₀ : ℕ) : D₀ ≤ D (logFour D₀) := Nat.le_pow_clog (by norm_num) D₀
















end Light.Sec4

end
end

section


/-!
# Corollaries 26 and 31 in the light language: rational parameters in the program text

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D";
proof of Corollary 31: "with L := ⌈cm⌉ and t := ⌈θm⌉". A program is a finite text, so it can hold c
and θ only if they are rational: c = a/b and θ = p/q (`RatParams`). For real c and θ the statements
follow by approximation (`exists_ratParams`). Corollary 26 is the case c = 21, θ = 1/9, with the
threshold 60 (`ratParams26`).

This file has the parameters, what a structure at the free pointer fr consists of (`structEnd`,
`Ready31`), what the routines ask of the limits (`Lim31`), the query with its specification and its
proof (`QuerySpec31`, `query31_meets`), and the text and the specification of the preprocessing
(`pre31Body`, `PreSpec31`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters -/
















variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}















/-- t ≤ m. -/
theorem RatParams.t_le (G : RatParams) (m : ℕ) : G.t m ≤ m := by
  unfold RatParams.t
  have hq := G.hq
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have h1 : 10 * G.p * m ≤ 9 * G.q * m := Nat.mul_le_mul_right _ G.hθ.le
  have h2 : G.p * m ≤ G.q * m := by
    have e1 : 10 * G.p * m = 10 * (G.p * m) := by ring
    have e2 : 9 * G.q * m = 9 * (G.q * m) := by ring
    omega
  omega





































/-- Below the threshold a structure has three cells. -/
theorem structEnd_small (h : logFour D₀ < G.m₀) (N fr : ℕ) : structEnd G N D₀ fr = fr + 3 :=
  if_pos h

/-- For m ≥ m₀ a structure ends with the block of Theorem 30. -/
theorem structEnd_large (h : G.m₀ ≤ logFour D₀) (N fr : ℕ) :
    structEnd G N D₀ fr = G.blockEnd N D₀ fr :=
  if_neg (not_lt.2 h)

/-- The block of Theorem 30 begins after the first three cells. -/
theorem add_three_le_blockAt (N D₀ fr : ℕ) : fr + 3 ≤ blockAt N D₀ fr := by
  unfold blockAt
  omega

/-- The block of Theorem 30 is not empty. -/
theorem RatParams.blockAt_lt_blockEnd (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr < G.blockEnd N D₀ fr :=
  base_lt_top _ _ _








/-- A structure has at least three cells. -/
theorem add_three_le_structEnd (G : RatParams) (N D₀ fr : ℕ) : fr + 3 ≤ structEnd G N D₀ fr := by
  have hblock := add_three_le_blockAt N D₀ fr
  have hend := G.blockAt_lt_blockEnd N D₀ fr
  by_cases h : logFour D₀ < G.m₀
  · rw [structEnd_small h]
  · rw [structEnd_large (not_lt.1 h)]
    omega


































/-- The numbers formed on the way to L fit in a word. -/
theorem Lim31.wordL (h : Lim31 lim G N D₀ fr U) : ((G.a * logFour D₀ + G.b : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast (by omega :
    G.a * logFour D₀ + G.b ≤ G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q)) h.mword

/-- The numbers formed on the way to t fit in a word. -/
theorem Lim31.wordT (h : Lim31 lim G N D₀ fr U) : ((G.p * logFour D₀ + G.q : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast (by omega :
    G.p * logFour D₀ + G.q ≤ G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q)) h.mword













theorem Input31.zero_le_U (h : Input31 lim G X Y aX aY fr U) : 0 ≤ U :=
  le_trans (abs_nonneg _) (h.absX ⟨0, h.one_le_N⟩ ⟨0, h.one_le_D⟩)

/-! ## The query: the text is query31Body -/













































































/-! ## The preprocessing: text and interface -/









namespace Pre31



















end Pre31















































end Light.Sec4

end
end

section


/-!
# Corollaries 26 and 31 in the light language: ⌈a m / b⌉ by counting

Proof of Corollary 26: "Let L := 21m and t := ⌈m/9⌉"; proof of Corollary 31: "with L := ⌈cm⌉ and t
:= ⌈θm⌉". For rational c = a/b the number ⌈a m / b⌉ is found without division: count in steps of b
up to a m. The numbers a and b are constants of the program text.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

namespace CeilMul








end CeilMul











theorem ceilMul_meets {lim : Limits} {P : Program} {pn a b : ℕ} (hb : 1 ≤ b)
    (hP : P[pn]? = some (ceilMulBody a b)) : CeilMulSpec lim P pn a b := by
  intro m μ hw
  refine fun d _ => ⟨ceilMulBody a b, hP, ?_⟩
  unfold ceilMulBody tCeilMul
  -- if m = 0
  refine Ends.iteLast (fun h0 => ?_) (fun h0 => ?_)
  · -- return m
    obtain rfl : m = 0 := by simpa using h0
    exact Ends.skip ⟨by simp [Nat.div_eq_of_lt (by omega : b - 1 < b)], rfl⟩
  · have hm : m ≠ 0 := by simpa using h0
    have hax : a ≤ a * m := Nat.le_mul_of_pos_right a (by omega)
    have hxZ : (a : ℤ) * m = (a * m : ℕ) := by push_cast; rfl
    generalize a * m = x at hw hax hxZ ⊢
    have hlt : ∀ i, i < (x + b - 1) / b ↔ i * b < x := fun i => Nat.lt_ceilDiv_iff hb
    have hnx : (x + b - 1) / b ≤ x := by
      by_contra hc
      have := (hlt x).1 (by omega)
      have := Nat.le_mul_of_pos_right x hb
      omega
    generalize (x + b - 1) / b = n at hlt hnx ⊢
    -- am := a * m ; c := 0 ; steps := 0
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen x ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hxZ]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hxZ] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hxZ] <;> omega)));
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
      (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
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
            0
              -- while c < am: c := c + b ; steps := steps + 1.  Before round i, c = i b and steps = i.
              
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
    -- while c < am: c := c + b ; steps := steps + 1.  Before round i, c = i b and steps = i.
    refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [m, x, ((i * b : ℕ) : ℤ), i], μ⟩) n
      (by simp) ?round ?done (hT := le_rfl))
    case round =>
      rintro i _ hi rfl
      have hbi := (hlt i).1 hi
      rw [Nat.succ_mul]
      generalize i * b = c at hbi ⊢
      exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                    ((try have := Light.Std.const_le (by assumption)));
                    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, by (((try have := Light.Std.space_le (by assumption)));
                                                                                                    ((try have := Light.Std.const_le (by assumption)));
                                                                                                    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩
    case done =>
      rintro _ rfl
      have hbn := mt (hlt n).2 (lt_irrefl n)
      generalize n * b = c at hbn ⊢
      -- return steps
      exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                    ((try have := Light.Std.const_le (by assumption)));
                    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, Ends.setTo (n : ℤ) ⟨rfl, rfl⟩⟩

end Light.Sec4

end
end

section


/-!
# Padding X with zero columns

Proof of Corollary 26: "pad the inner dimension to 4^m < 4D with zero columns of X". Row by row: a
copy of the row and a fill with zeros. The invariant `PadX.Rows` says that the first i rows of the
padded matrix have been written; `PadX.Rows.succ` is what a round does to the memory, and
`padX_meets` the specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace PadX











end PadX









namespace PadX

variable {N D₀ D' aX aX' i : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {μ μ' μ₁ μ₂ : ℕ → ℤ}







/-- A round: row i of X has been copied, and zeros have been written behind it. -/
theorem Rows.succ (h : Rows μ aX' D' X i μ') (hX : MatAt μ aX X) (hsep : aX + N * D₀ ≤ aX')
    (hi : i < N) (hcopy : ∀ j < D₀, μ₁ (aX' + i * D' + j) = μ' (aX + i * D₀ + j))
    (hout₁ : SameOutside μ' μ₁ (aX' + i * D') D₀)
    (hfill : ∀ j < D' - D₀, μ₂ (aX' + i * D' + D₀ + j) = 0)
    (hout₂ : SameOutside μ₁ μ₂ (aX' + i * D' + D₀) (D' - D₀)) (hDD : D₀ ≤ D') :
    Rows μ aX' D' X (i + 1) μ₂ := by
  have hrow : i * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul hi le_rfl
  refine ⟨fun r j hr => ?_, fun b hb => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
    · -- an earlier row lies below the cells that the round has written
      have := Nat.mul_add_lt_mul hlt j.isLt
      rw [hout₂ _ (.inl (by omega)), hout₁ _ (.inl (by omega))]
      exact h.1 r j hlt
    · by_cases hj : (j : ℕ) < D₀
      · -- an entry of X, which is as at the start
        rw [heq, hout₂ _ (.inl (by omega)), hcopy _ hj, h.2 _ (.inl (by omega)), padInnerCols,
          dif_pos hj, ← heq]
        exact hX r ⟨j, hj⟩
      · -- a zero
        have hcell : aX' + (r : ℕ) * D' + (j : ℕ) = aX' + i * D' + D₀ + ((j : ℕ) - D₀) := by
          rw [heq]; omega
        rw [hcell, hfill _ (by have := j.isLt; omega), padInnerCols, dif_neg hj]
  · rw [Nat.succ_mul] at hb
    rw [hout₂ b (by omega), hout₁ b (by omega), h.2 b (by omega)]

end PadX

open PadX in
theorem padX_meets {lim : Limits} {P : Program} (hP : P[Proc.padX]? = some padXBody)
    (hcopy : CopySpec lim P) (hfill : FillSpec lim P) (hstd : Std lim) : PadXSpec lim P := by
  intro N D₀ D' aX aX' X μ hDD hD1 hX hsep hsp
  refine fun d hd => ⟨padXBody, hP, ?_⟩
  have hw := hstd.space_le
  have h100 := hstd.const_le
  have hN : N ≤ N * D' := Nat.le_mul_of_pos_right _ hD1
  have hsub : (D' : ℤ) - D₀ = ((D' - D₀ : ℕ) : ℤ) := (Nat.cast_sub hDD).symm
  unfold padXBody tPadX
  -- for i < N
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame [N, D₀, D', aX, aX', i, r], μ'⟩ ∧ Rows μ aX' D' X i μ') N (16 * D' + 60)
    ?start ?round ?done ?bound
  case start =>
    exact ⟨0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl,
      fun r j hr => absurd hr (Nat.not_lt_zero _), fun _ _ => rfl⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨r, μ', rfl, hrows, hout⟩
    exact ⟨fun r j => hrows r j r.isLt, hout⟩
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hrows⟩
    -- row i of X and row i of the padded matrix lie within their arrays
    have hsrc : i * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul hi le_rfl
    have hdst : i * D' + D' ≤ N * D' := Nat.mul_add_le_mul hi le_rfl
    -- copy(aX + i D, aX' + i D', D)
    refine Ends.callToThen (hcopy (aX + i * D₀) (aX' + i * D') D₀ μ' (by omega) (by omega)
      (by omega) (.inl (by omega)) _ (by omega)) ?_ (hT := by simp [tCopy]; omega)
    rintro - μ₁ ⟨hc, hout₁⟩
    -- fill(aX' + i D' + D, D' - D, 0)
    refine Ends.callTo (hfill (aX' + i * D' + D₀) (D' - D₀) 0 μ₁ (by omega) (by omega) _
      (by omega)) ?_ (by (((try have := Light.Std.space_le (by assumption)));
                           ((try have := Light.Std.const_le (by assumption)));
                           (simp [Light.Limits.Addr, abs_le, -abs_mul, hsub] <;> omega))) (hT := by simp [tCopy, tFill]; omega)
    rintro r' μ₂ ⟨hf, hout₂⟩
    exact ⟨by simp, r', μ₂, by rw [update_frame_setLocal]; rfl,
      hrows.succ hX hsep hi hc hout₁ hf hout₂ hDD⟩

end Light.Sec4

end
end

section


/-!
# Corollaries 26 and 31 in the light language: the preprocessing, with rational parameters

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D with
zero columns of X and zero rows of Y." Proof of Corollary 31: "We repeat the proof of Corollary 26
with L := ⌈cm⌉ and t := ⌈θm⌉". Then the preprocessing of Theorem 30 on the padded matrices; "for
smaller m the corollary again holds trivially".

The routine meets its specification (`pre31_meets`). It computes m and branches. Below the threshold
it writes the flag 0 (`PreInput31.ready_small`). From the threshold on it computes L, t and the
addresses, pads X, and pads Y by a copy and a fill with zeros (`prePad31_ends`,
`matAt_padInnerRows`); then it calls the preprocessing of Theorem 30 and writes the base address and
the flag 1 (`preBuild31_ends`, `PreInput31.ready_large`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## What the routine is given, and what it leaves -/



















/-- Below the threshold the flag 0 is all that a query needs. -/
theorem PreInput31.ready_small (h : PreInput31 lim G X Y aX aY fr U μ) (hm : logFour D₀ < G.m₀)
    (hkept : SameOn (· < fr) μ μ') (hflag : μ' fr = 0) : Ready31 G X Y aX aY fr μ' :=
  ⟨h.matX.congr_below hkept h.belowX, h.matY.congr_below hkept h.belowY, fun _ => hflag,
    fun hm' => absurd hm' (by omega)⟩

/-- From the threshold on a query needs the flag 1, the base address, and the data structure of
Theorem 30 for the padded matrices. -/
theorem PreInput31.ready_large (h : PreInput31 lim G X Y aX aY fr U μ) (hm : G.m₀ ≤ logFour D₀)
    (hkept : SameOn (· < fr) μ μ') (hflag : μ' fr = 1) (hbase : μ' (fr + 1) = blockAt N D₀ fr)
    (hDS : Built31 G X Y fr μ') : Ready31 G X Y aX aY fr μ' :=
  ⟨h.matX.congr_below hkept h.belowX, h.matY.congr_below hkept h.belowY,
    fun hm' => absurd hm (by omega), fun _ => ⟨hflag, hbase, hDS⟩⟩

/-- **Y with zero rows**: a copy of Y followed by zeros is the padded matrix. -/
theorem matAt_padInnerRows {F a : ℕ} (mY : MatAt μ aY Y)
    (hcopy : ∀ i < D₀ * N, μ' (a + i) = μ (aY + i))
    (hzero : ∀ i < (F - D₀) * N, μ' (a + D₀ * N + i) = 0) : MatAt μ' a (padInnerRows F Y) := by
  intro i j
  unfold padInnerRows
  by_cases hi : (i : ℕ) < D₀
  · rw [dif_pos hi, Nat.add_assoc, hcopy _ (Nat.mul_add_lt_mul hi j.isLt), ← Nat.add_assoc]
    exact mY ⟨i, hi⟩ j
  · have hrow : (i : ℕ) * N = D₀ * N + ((i : ℕ) - D₀) * N := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' (not_lt.mp hi)]
    have hidx := Nat.mul_add_lt_mul (by have := i.isLt; omega : (i : ℕ) - D₀ < F - D₀) j.isLt
    rw [dif_neg hi, hrow, ← Nat.add_assoc, Nat.add_assoc (a + D₀ * N), hzero _ hidx]

/-! ## From the threshold on -/












theorem PreInput31.areas (h : PreInput31 lim G X Y aX aY fr U μ) (hm : G.m₀ ≤ logFour D₀) :
    Areas31 lim N D₀ fr (D (logFour D₀)) ((D (logFour D₀) - D₀) * N) where
  F_eq := rfl
  R_eq := rfl
  base := rfl
  base_lt := (G.blockAt_lt_blockEnd N D₀ fr).trans_le (structEnd_large hm N fr ▸ h.lim.space)
  D_le := le_D_logFour D₀
  rows := by rw [← Nat.add_mul, Nat.add_sub_cancel' (le_D_logFour D₀), Nat.mul_comm]
  F_le := Nat.le_mul_of_pos_left _ h.one_le_N



















/-- **Setting up**: L, t, the addresses, and the padded matrices. The cell fr + 2 holds 4^m. -/
theorem prePad31_ends {c d : ℕ} (C : PreCalls31 lim P c G) (h : PreInput31 lim G X Y aX aY fr U μ)
    (hm : G.m₀ ≤ logFour D₀) (hd : d + (G.L (logFour D₀) + 7) ≤ lim.depth) :
    Ends lim P d prePad31
      ⟨frame [N, D₀, aX, aY, fr, logFour D₀], Function.update μ (fr + 2) ((D (logFour D₀) : ℕ) : ℤ)⟩
      (tPrePad31 G N D₀) (Padded31 G X Y aX aY fr μ) := by
  have A := h.areas hm
  unfold prePad31 tPrePad31 Padded31 paddedXAt paddedYAt
  rw [A.base]
  generalize D (logFour D₀) = F at A ⊢
  generalize (F - D₀) * N = R at A ⊢
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁, μ₁ = Function.update μ (fr + 2) ((F : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hμ₁]
  obtain ⟨-, hR, hb0, hb0lt, hDF, hrows, hFN⟩ := A
  have hw := h.lim.std.space_le
  have h100 := h.lim.std.const_le
  have hD := h.one_le_D
  have hbX := h.belowX
  have hbY := h.belowY
  have hRZ : ((F : ℤ) - D₀) * N = R := by rw [hR]; push_cast [Nat.cast_sub hDF]; rfl
  have hread : μ₁ (fr + 2) = F := by rw [hμ₁]; exact Function.update_self ..
  have hout₁ : SameOutside μ μ₁ (fr + 2) 1 := hμ₁ ▸ SameOn.refl.write (by omega) _
  have hkept₁ : ∀ b < fr, μ₁ b = μ b := fun b hb => hout₁ b (.inl (by omega))
  have haddr : ((fr : ℤ) + 2).toNat = fr + 2 := by omega
  -- F := mem[fr + 2]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen F ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddr,
                hread]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [haddr, hread] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hread] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- L := ⌈a m / b⌉
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
            ((C.levels (logFour D₀) μ₁ h.lim.wordL _ (by omega)) _ (by omega)) ?_
            ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.levels (logFour D₀) μ₁ h.lim.wordL _ (by omega)) ?_ ?_ ?_ ?_);
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
        ((rintro _ μ₁
              ⟨rfl, rfl⟩
                  -- t := ⌈p m / q⌉
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- t := ⌈p m / q⌉
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
            ((C.switch (logFour D₀) μ₁ h.lim.wordT _ (by omega)) _ (by omega)) ?_
            ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.switch (logFour D₀) μ₁ h.lim.wordT _ (by omega)) ?_ ?_ ?_ ?_);
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
        ((rintro _ μ₁
              ⟨rfl, rfl⟩
                  -- aX' := fr + 3 ; NF := N * F ; aY' := aX' + NF ; b0 := aY' + NF
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- aX' := fr + 3 ; NF := N * F ; aY' := aX' + NF ; b0 := aY' + NF
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (fr + 3 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (N * F : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (fr + 3 + N * F : ℕ) ?_ ?_ ?_);
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
          (fr + 3 + N * F + N * F : ℕ)
            -- padX(N, D, F, aX, aX')
            
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
  -- padX(N, D, F, aX, aX')
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
            ((C.padX N D₀ F aX (fr + 3) X μ₁ hDF (by omega)
                (h.matX.congr_below hkept₁ hbX) (by omega) (by omega) _
                (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.padX N D₀ F aX (fr + 3) X μ₁ hDF (by omega)
              (h.matX.congr_below hkept₁ hbX) (by omega) (by omega) _ (by omega))
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
        ((rintro - μ₂
              ⟨hpadX, hout₂⟩
                  -- copy(aY, aY', D N)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- copy(aY, aY', D N)
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
            ((C.copy aY (fr + 3 + N * F) (D₀ * N) μ₂ (by omega) (by omega)
                (by omega) (.inl (by omega)) _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.copy aY (fr + 3 + N * F) (D₀ * N) μ₂ (by omega) (by omega)
              (by omega) (.inl (by omega)) _ (by omega))
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
        ((rintro - μ₃
              ⟨hcopy, hout₃⟩
                  -- fill(aY' + D N, (F - D) N, 0)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- fill(aY' + D N, (F - D) N, 0)
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
            ((C.fill (fr + 3 + N * F + D₀ * N) R 0 μ₃ (by omega) (by omega) _
                (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.fill (fr + 3 + N * F + D₀ * N) R 0 μ₃ (by omega) (by omega) _
              (by omega))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hRZ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hRZ] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hRZ] <;> omega)));
    (on_goal -1 =>
        ((rintro r μ₄ ⟨hfill, hout₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨r, μ₄, rfl, ?_, ?_, fun b hb => ?_⟩
  · exact hpadX.congr fun b _ hb => by rw [hout₄ b (.inl (by omega)), hout₃ b (.inl (by omega))]
  · refine matAt_padInnerRows (h.matY.congr_below hkept₁ hbY) (fun i hi => ?_) (hR ▸ hfill)
    rw [hout₄ _ (.inl (by omega)), hcopy i hi, hout₂ _ (.inl (by omega))]
  · rw [hout₄ b (by omega), hout₃ b (by omega), hout₂ b (by omega), hout₁ b (by omega)]

/-- **The preprocessing of Theorem 30** on the padded matrices, the base address and the flag 1. -/
theorem preBuild31_ends {c d : ℕ} (C : PreCalls31 lim P c G) (h : PreInput31 lim G X Y aX aY fr U μ)
    (hm : G.m₀ ≤ logFour D₀) (hd : d + (G.L (logFour D₀) + 7) ≤ lim.depth) {σ : State}
    (hσ : Padded31 G X Y aX aY fr μ σ) :
    Ends lim P d preBuild31 σ (tPreCore c (parOf G N D₀) (switchOf31 G D₀) + 60) fun σ' =>
      Ready31 G X Y aX aY fr σ'.mem ∧ SameOutside μ σ'.mem fr (structEnd G N D₀ fr - fr) := by
  obtain ⟨r, μ₄, rfl, mX, mY, hout₄⟩ := hσ
  have hb0 := (h.areas hm).base
  have hb0lt := (h.areas hm).base_lt
  have hw := h.lim.std.space_le
  have h100 := h.lim.std.const_le
  have hb0top := G.blockAt_lt_blockEnd N D₀ fr
  have hfr3 := add_three_le_structEnd G N D₀ fr
  unfold preBuild31
  -- preCore(L, m, t, N, F, aX', aY', b0)
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
            ((C.preCore (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr) (paddedYAt N D₀ fr) (blockAt N D₀ fr) _ _ U μ₄ (G.t_le _) (h.lim.large hm) (abs_padInnerCols_le h.absX h.zero_le_U)
                (abs_padInnerRows_le h.absY h.zero_le_U) mX mY (by (change fr + 3 + N * D (logFour D₀) ≤ _); (omega)) (by (change fr + 3 + N * D (logFour D₀) + D (logFour D₀) * N ≤ _); (rw [Nat.mul_comm (D (logFour D₀)) N]); (omega)) _
                (by (change d + 1 + (G.L (logFour D₀) + 6) ≤ _); (omega)))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (C.preCore (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr) (paddedYAt N D₀ fr) (blockAt N D₀ fr) _ _ U μ₄ (G.t_le _) (h.lim.large hm) (abs_padInnerCols_le h.absX h.zero_le_U)
              (abs_padInnerRows_le h.absY h.zero_le_U) mX mY (by (change fr + 3 + N * D (logFour D₀) ≤ _); (omega)) (by (change fr + 3 + N * D (logFour D₀) + D (logFour D₀) * N ≤ _); (rw [Nat.mul_comm (D (logFour D₀)) N]); (omega)) _
              (by (change d + 1 + (G.L (logFour D₀) + 6) ≤ _); (omega)))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, parOf, switchOf31, Sec2.Par.D]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [parOf, switchOf31, Sec2.Par.D] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega); (on_goal -1 => (((try have := Light.Std.space_le (by assumption))); ((try have := Light.Std.const_le (by assumption))); (simp [Light.Limits.Addr, abs_le, -abs_mul, parOf, switchOf31, Sec2.Par.D] <;> omega)));
    (on_goal -1 => ((rintro - μ₅ ⟨hDS, hout₅⟩); (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hout₅ : SameOutside μ₄ μ₅ (blockAt N D₀ fr) (G.blockEnd N D₀ fr - blockAt N D₀ fr) := hout₅
  -- mem[fr + 1] := b0
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
        Light.Ends.storeToThen (fr + 1)
          (blockAt N D₀ fr)
            -- mem[fr] := 1
            
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
  -- mem[fr] := 1
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
        Light.Ends.storeToThen fr
          1
            -- outside the cells from fr to the end of the block nothing has changed
            
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
  -- outside the cells from fr to the end of the block nothing has changed
  have hsame : SameOutside μ μ₅ fr (structEnd G N D₀ fr - fr) := by
    rw [structEnd_large hm]
    exact fun b hb => (hout₅ b (by omega)).trans (hout₄ b (by omega))
  dsimp only
  refine ⟨h.ready_large hm (fun b (hb : b < fr) => ?_) (Function.update_self ..) ?_
    (dsReady_congr hDS fun a ha => ?_), (hsame.write (by omega) _).write (by omega) _⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hsame b (.inl hb)]
  · rw [Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-! ## The routine -/

theorem pre31_meets {c : ℕ} (G : RatParams) (hP : P[Proc.pre31]? = some (pre31Body G))
    (C : PreCalls31 lim P c G) : PreSpec31 lim P c G :=
        by
  intro N D₀ aX aY fr X Y U μ hin mX mY
  have h : PreInput31 lim G X Y aX aY fr U μ := ⟨hin, mX, mY⟩
  have hlim := hin.lim
  refine fun d hd => ⟨pre31Body G, hP, ?_⟩
  have hw := hlim.std.space_le
  have h100 := hlim.std.const_le
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hsp := hlim.space
  have hm₀word := hlim.m0word
  have hmword : (logFour D₀ : ℤ) ≤ lim.word := by
    have : logFour D₀ ≤ G.a * logFour D₀ := Nat.le_mul_of_pos_left _ (by have := G.hc; omega)
    exact le_trans (by exact_mod_cast (by omega :
      logFour D₀ ≤ G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q)) hlim.mword
  unfold pre31Body
  -- m := log4(D, fr + 2), which writes 4^m to the cell fr + 2
  refine Ends.callToThen (C.log4 D₀ (fr + 2) μ (by omega) hlim.pow hmword _ (by omega)) ?_
    (hT := by simp [tPre31, logFour]; omega)
  rintro _ _ ⟨rfl, rfl⟩
  -- if m < m₀
  refine Ends.iteLast (fun hsmall => ?_) (fun hlarge => ?_) (hT := by simp [tPre31, logFour]; omega)
  · -- mem[fr] := 0
    have hm : logFour D₀ < G.m₀ := by simpa [logFour] using hsmall
    have htop : structEnd G N D₀ fr - fr = 3 := by rw [structEnd_small hm]; omega
    refine Ends.storeTo fr 0 ⟨h.ready_small hm (fun b (hb : b < fr) => ?_)
      (Function.update_self ..), ?_⟩ (hT := by simp [tPre31, logFour]; omega)
    · change Function.update (Function.update μ _ _) fr 0 b = μ b
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rw [htop]
      exact (SameOn.refl.write (by omega) _).write (by omega) _
  · have hm : G.m₀ ≤ logFour D₀ := by simpa [logFour] using hlarge
    -- the padded matrices, then the data structure of Theorem 30
    refine Ends.next (tPrePad31 G N D₀) ((prePad31_ends C h hm hd).mono le_rfl fun σ hσ =>
      (preBuild31_ends C h hm hd hσ).mono ?_ fun _ hQ => hQ) ?_
    all_goals
      simp only [tPre31, tPrePad31, if_neg (not_lt.mpr hm)]
      simp [logFour]
      omega

end Light.Sec4

end
end

section


/-!
# The block of Theorem 30: the directory, sizes and limits

Facts about the memory map and the invariant DSReady that the preprocessing and the query (proof of
Theorem 30) share.

* `dir_cell` gives a cell of the directory.
* The roots fill their area and the tries fit into theirs (`length_dsTries_roots`,
  `length_dsTries_le`).
* The limits: 10^L fits in a word (`Lim30.pow_le`), and the encoded numbers are at most 7^L U
  (`abs_enc_le`).
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {U : ℤ}
  {μ μ' : ℕ → ℤ}

/-! ## The directory -/

/-- A cell of the directory. -/
theorem dir_cell (h : Sec2.SharedReady p hmL aX aY b0 X Y μ) {j : ℕ} (hj : j < 31) :
    μ (b0 + j) = (((Sec2.dirList p aX aY b0).getD j 0 : ℕ) : ℤ) :=
  h.dir.read (by simpa [Sec2.dirList] using hj)

/-! ## Sizes and limits -/
















/-- The number 10^L of leaves fits in a word. -/
theorem Lim30.pow_le (h : Lim30 lim p t b0 U) : (10 : ℤ) ^ p.L ≤ lim.word := by
  refine le_trans ?_ h.pow
  push_cast
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Proof of Theorem 30, "Word size": the encoded numbers are at most 7^L U in absolute value. -/
theorem abs_enc_le (hmL : p.m ≤ p.L) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (U : ℤ) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (β β' : ℕ) :
    (∀ τ, |encRow p hmL X β τ| ≤ 7 ^ p.L * U) ∧ ∀ τ, |encCol p hmL Y β' τ| ≤ 7 ^ p.L * U := by
  exact ⟨abs_encodingL_le (abs_bandArrayL_le (stdLayout hmL) hU hX β),
    abs_encodingR_le (abs_bandArrayR_le (stdLayout hmL) hU hY β')⟩

end Light.Sec4

end
end

section


/-!
# The cells of the directory, by name

The routines of Section 4 find the sizes and the addresses of the tables in the directory, the
first cells of the block.  `DirCells p b0 μ` says what the cells that they read hold, one equation
for each cell, under the name that the cell has in the program texts (`Dir.bands`, `Dir.encA`, …).
A proof that treats `x := mem[b0 + Dir.bands]` names the equation `bands`.  The shared stage
establishes all of them (`SharedReady.dirCells`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

















/-- After the shared stage the directory holds what `DirCells` says. -/
theorem _root_.Light.Sec2.SharedReady.dirCells {p : Sec2.Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
    {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ : ℕ → ℤ}
    (h : Sec2.SharedReady p hmL aX aY b0 X Y μ) : DirCells p b0 μ where
  levels := dir_cell h (j := Dir.levels) (by norm_num)
  inner := dir_cell h (j := Dir.inner) (by norm_num)
  outer := h.dir_read (j := Dir.outer) (by norm_num)
  blocks := h.dir_read (j := Dir.blocks) (by norm_num)
  bands := h.dir_read (j := Dir.bands) (by norm_num)
  leaves := h.dir_read (j := Dir.leaves) (by norm_num)
  mask := h.dir_read (j := Dir.mask) (by norm_num)
  band := h.dir_read (j := Dir.band) (by norm_num)
  block := h.dir_read (j := Dir.block) (by norm_num)
  digits := h.dir_read (j := Dir.digits) (by norm_num)
  encA := h.dir_read (j := Dir.encA) (by norm_num)
  encB := h.dir_read (j := Dir.encB) (by norm_num)
  sharedEnd := h.dir_read (j := Dir.sharedEnd) (by norm_num)

end Light.Sec4

end
end

section


/-!
# The preprocessing of Theorem 30, at a given place of the memory

Proof of Theorem 30, "Preprocessing". The routine first runs the stage that it shares with
Theorem 5: the list of the subsets, the tables for the rows and columns, and the encodings of all
row bands and column bands. It notes t in the directory, computes the addresses of the areas of
Section 4 (preCoreAddr), starts the trie area with the array [0], and computes the values of all the
boxes of all tiles, by Lemma 29 (preCoreFinish). There is one lemma for each of the two named parts;
preCore_spec puts them behind the shared stage.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace PreCore






















end PreCore







































variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The addresses -/

/-- The addresses of the areas of Section 4 are computed as the map says. -/
theorem preCoreAddr_spec (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U)
    (hSR : Sec2.SharedReady p hmL aX aY b0 X Y μ) (r : ℤ) :
    Ends lim P d preCoreAddr ⟨frame (preShared p t aX aY b0 r), μ⟩ 38
      (· = ⟨frame (preLocals p t aX aY b0 r), μ⟩) := by
  have dir := hSR.dirCells
  ((obtain ⟨⟩ := id hlim); (obtain ⟨⟩ := id hlim.std))
  obtain ⟨⟩ := areas p t b0
  unfold preLocals preShared
  -- the product nB², in the integers
  have hsq : ((p.nB * p.nB : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.nB * p.nB ≤ lim.space)
  have htr : ((aROOTS p b0 + p.nB * p.nB : ℕ) : ℤ) = aTR p b0 := by
    exact_mod_cast (by omega : aROOTS p b0 + p.nB * p.nB = aTR p b0)
  have hsq0 : (0 : ℤ) ≤ (p.nB : ℤ) * p.nB := by positivity
  push_cast at hsq htr
  -- digits := dir[30]; bands := dir[9]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aWD p b0 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.sharedEnd]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.sharedEnd] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.sharedEnd] <;> omega)));
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
    (refine Light.Ends.setToThen (p.nB : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                dir.bands]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [dir.bands] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, dir.bands] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- cur := digits + L; box := cur + L; free := box + L + m; roots := free + 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aCUR p b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (aBOX p b0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (aFP p b0 : ℕ) ?_ ?_ ?_);
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
          (aROOTS p b0 : ℕ)
            -- last := m - t; tries := roots + nB nB
            
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
  -- last := m - t; tries := roots + nB nB
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (p.m - t : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (aTR p b0 : ℕ) ?_ ?_ ?_);
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

/-! ## The tries -/




















/-- The block, after the shared stage and with the trie array [0], holds what allTiles assumes. -/
theorem allArgs_pre (h : Lim30 lim p t b0 U) (ht : t ≤ p.m) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hSR : Sec2.SharedReady p hmL aX aY b0 X Y μ)
    (hTM : TrieMem μ (aTR p b0) (trieCap p t) (aFP p b0) [0]) :
    AllTilesPre lim μ (allArgs p t hmL b0 X Y) := by
  -- a negative bound U is possible only if there are no entries; then 0 is a bound as well
  obtain ⟨U', hU0, hX', hY', hvalue⟩ : ∃ U' : ℤ, 0 ≤ U' ∧ (∀ i j, |X i j| ≤ U') ∧
      (∀ i j, |Y i j| ≤ U') ∧ 10 ^ p.m * ((7 ^ p.L * U') * (7 ^ p.L * U')) ≤ lim.word := by
    rcases le_or_gt 0 U with h0 | h0
    · exact ⟨U, h0, hX, hY, h.value⟩
    · have hword : (0 : ℤ) ≤ lim.word := le_trans (by norm_num) h.std.const_le
      exact ⟨0, le_rfl, fun i j => absurd ((abs_nonneg _).trans (hX i j)) (not_le.mpr h0),
        fun i j => absurd ((abs_nonneg _).trans (hY i j)) (not_le.mpr h0), by simpa using hword⟩
  have hsp := h.space
  have hT : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  exact
    { std := h.std
      t_le := ht
      m_le := hmL
      value_le := ⟨7 ^ p.L * U', 7 ^ p.L * U',
        fun β τ => (abs_enc_le hmL X Y U' hU0 hX' hY' β β).1 τ,
        fun β τ => (abs_enc_le hmL X Y U' hU0 hX' hY' β β).2 τ, hvalue⟩
      pow_le := h.pow_le
      cap_ge := le_rfl
      order := by simp only [allArgs]; rw [hT]; omega
      segA := fun β hβ => hSR.encA β hβ
      segB := fun β hβ => hSR.encB β hβ
      trie := hTM }

/-- The trie area with the array [0], after the two stores. -/
theorem trieMem_start (p : Sec2.Par) (t b0 : ℕ) (μ : ℕ → ℤ) :
    TrieMem (Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1) (aTR p b0)
      (trieCap p t) (aFP p b0) [0] := by
  obtain ⟨⟩ := areas p t b0
  refine ⟨fun i hi => ?_, Function.update_self .., by simp [trieCap], Or.inl (by omega)⟩
  obtain rfl : i = 0 := by simpa using hi
  rw [Nat.add_zero, Function.update_of_ne (by omega), Function.update_self]
  rfl

/-- After the shared stage, the last part completes the data structure; it changes only cells from
CUR to the end of the block. -/
theorem preCoreFinish_spec (hAll : AllTilesSpec lim P) (hlim : Lim30 lim p t b0 U) (ht : t ≤ p.m)
    (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (hd : d + 5 ≤ lim.depth) (r : ℤ)
    (hSR : Sec2.SharedReady p hmL aX aY b0 X Y μ) (hcellT : μ (b0 + 31) = t) :
    Ends lim P d preCoreFinish ⟨frame (preLocals p t aX aY b0 r), μ⟩
      (tAllTiles p.L p.m t p.nB + 28) fun σ' =>
      DSReady p t hmL aX aY b0 X Y σ'.mem ∧
        SameOutside μ σ'.mem (aCUR p b0) (top p t b0 - aCUR p b0) := by
  ((obtain ⟨⟩ := id hlim); (obtain ⟨⟩ := id hlim.std))
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold preLocals preShared
  -- TR[0] := 0; FP := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen (aTR p b0) 0 ?_ ?_ ?_);
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
    (refine Light.Ends.storeToThen (aFP p b0) 1 ?_ ?_ ?_);
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
  have hTM := trieMem_start p t b0 μ
  have same : SameOutside μ (Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1)
      (aCUR p b0) (top p t b0 - aCUR p b0) :=
    (SameOutside.refl.update (by omega) 0).update (by omega) 1
  generalize Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1 = μ₁ at *
  have hSR₁ : Sec2.SharedReady p hmL aX aY b0 X Y μ₁ :=
    hSR.of_agree fun b hb _ => same b (Or.inl (by omega))
  have dir := hSR₁.dirCells
  -- the tries of all tiles
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
            ((hAll _ μ₁ (allArgs_pre hlim ht hX hY hSR₁ hTM)) _ (by omega)) ?_ ?_
            ?_ ?_
      |
        refine
          Light.Ends.callToThen (hAll _ μ₁ (allArgs_pre hlim ht hX hY hSR₁ hTM))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, allArgs,
                dir.encA, dir.encB, dir.leaves, Sec2.Par.T]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [allArgs, dir.encA, dir.encB, dir.leaves, Sec2.Par.T] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, allArgs, dir.encA, dir.encB,
                dir.leaves, Sec2.Par.T] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r' μ₂ ⟨hTM₂, hroots, same₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have same' : SameOutside μ μ₂ (aCUR p b0) (top p t b0 - aCUR p b0) :=
    same.then same₂ fun b hb =>
      ⟨hb, by change b < aCUR p b0 ∨ aTR p b0 + trieCap p t ≤ b; omega⟩
  exact ⟨⟨hSR.of_agree fun b hb _ => same' b (Or.inl (by omega)),
    (same' _ (Or.inl (by omega))).trans hcellT, hroots, hTM₂.seg⟩, same'⟩

/-! ## The routine -/

/-- **preCore** meets its specification. -/
theorem preCore_spec {c : ℕ} (hP : P[Proc.preCore]? = some preCoreBody)
    (hShared : Sec2.SharedSpec lim P c) (hAll : AllTilesSpec lim P) : PreCoreSpec lim P c := by
  intro p t hmL aX aY b0 X Y U μ ht hlim hX hY hMX hMY haX haY
  refine fun d hd => ⟨preCoreBody, hP, ?_⟩
  ((obtain ⟨⟩ := id hlim); (obtain ⟨⟩ := id hlim.std))
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold tPreCore
  -- the shared stage
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
            ((hShared p hmL aX aY b0 μ X Y U
                { space := by omega, matX := hMX, matY := hMY, belowX := haX,
                  belowY := haY, absX := hX
                  absY := hY, seven := hlim.enc, ten := hlim.pow })
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (hShared p hmL aX aY b0 μ X Y U
              { space := by omega, matX := hMX, matY := hMY, belowX := haX,
                belowY := haY, absX := hX
                absY := hY, seven := hlim.enc, ten := hlim.pow })
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
        ((rintro r μ₁
              ⟨hSR₁, same₁⟩
                  -- dir[31] := t
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- dir[31] := t
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen (b0 + 31) t ?_ ?_ ?_);
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
  have hSR₂ : Sec2.SharedReady p hmL aX aY b0 X Y (Function.update μ₁ (b0 + 31) t) :=
    hSR₁.of_agree fun b _ hb => Function.update_of_ne hb ..
  -- the addresses
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (preCoreAddr_spec ht hlim hSR₂ r) ?_ ?_
      | refine Light.Ends.pieceLast (preCoreAddr_spec ht hlim hSR₂ r) ?_ ?_);
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
    (on_goal -1 => rintro _ rfl)
  -- the tries
  refine (preCoreFinish_spec hAll hlim ht hX hY (by omega) r hSR₂ (Function.update_self ..)).mono
    (by simp; omega) ?_
  rintro σ' ⟨hDS, same₂⟩
  refine ⟨hDS, fun b hb => ?_⟩
  rw [same₂ b (by omega), Function.update_of_ne (by omega), same₁ b (by omega)]

end Light.Sec4

end
end

section


/-!
# The routines of Section 4, assembled

The fourteen routines with the numbers 40 to 53, as a list (procs40), and the theorem that every
program that holds them at these numbers (Has40) meets all their specifications (specs40). Each
routine is proved under the specifications of the routines that it calls; here these assumptions are
discharged, in the order in which the routines call each other. For the programs of Theorem 30, its
offline form and Corollary 26, which hold the fourteen routines behind forty others
(has40_of_append), this gives the specifications of the two routines that know the memory map:
preCoreSpec_of and preCoreSpec_all for the preprocessing, queryAtSpec_all for a query.
-/

@[expose] public section

namespace Light.Sec4


















































/-- The preprocessing at a given place of the memory, for a program that also holds its body and
meets the specification of the shared stage. -/
theorem preCoreSpec_of {lim : Limits} {P : Program} {c : ℕ} (h : Has40 P)
    (h54 : P[Proc.preCore]? = some preCoreBody) (hs : Std lim)
    (hShared : Sec2.SharedSpec lim P c) : PreCoreSpec lim P c :=
  preCore_spec h54 hShared (specs40 h hs).allTiles

/-- The same for all limits: the specification assumes Lim30, which contains the standing
assumptions. -/
theorem preCoreSpec_all {P : Program} {c : ℕ} (h : Has40 P)
    (h54 : P[Proc.preCore]? = some preCoreBody)
    (hShared : ∀ lim, Std lim → Sec2.SharedSpec lim P c) : ∀ lim, PreCoreSpec lim P c :=
  fun lim p t hmL aX aY b0 X Y U μ ht hlim =>
    preCoreSpec_of h h54 hlim.std (hShared lim hlim.std) p t hmL aX aY b0 X Y U μ ht hlim








/-- A list that has forty procedures, then the routines of Section 4, then anything, holds them at
their numbers. -/
theorem has40_of_append {A B : List Stmt} (hA : A.length = 40) : Has40 (A ++ procs40 ++ B) := by
  intro i hi
  have hlen : procs40.length = 14 := rfl
  rw [List.append_assoc, List.getElem?_append_right (by omega), hA, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by omega)]

end Light.Sec4

end
end

section


/-!
# Theorem 30 on the word RAM: the program

`program30` is the list of procedures: those of Section 2 (numbers 0 to 28, of which the
preprocessing uses the shared stage), the routines of Section 4 (40 to 53), preCore, queryAt and the
two procedures of the offline form (54 to 57), and the two main procedures of Theorem 30 (80 and
81); the unused numbers hold the empty statement.

The first 58 procedures (`base58`) are also the beginning of the programs for Corollaries 26, 31
and 32.  So the assumptions of the earlier files are discharged for every program `base58 ++ R` that
begins with them: it meets the specifications of the preprocessing and of a query at a given place
of the memory (`preCore_base58`, `queryAt_base58`).  With `theorem_30_of` and `theorem_30_wanted_of`
this gives Theorem 30 and its offline form without hypotheses (`wordRam_theorem_30`,
`wordRam_theorem_30_wanted`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam








theorem length_base58 : base58.length = 58 := rfl

/-- A procedure of base58 is a procedure, with the same number, of every program that begins with
base58. -/
theorem at_base58 {p : ℕ} {body : Stmt} (h : base58[p]? = some body) (R : Program) :
    (base58 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R




theorem has40_base58 (R : Program) : Has40 (base58 ++ R) := by
  have h := has40_of_append (A := Sec2.programThin ++ List.replicate 11 .skip)
    (B := [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody] ++ R) rfl
  rwa [← List.append_assoc] at h

/-- The shared stage, in every program that begins with base58. -/
theorem shared_base58 (R : Program) (lim : Limits) (std : Std lim) :
    Sec2.SharedSpec lim (base58 ++ R) cShared30 := by
  have e : base58 ++ R = Sec2.program5 ++
      ([Sec2.regimeBody, Sec2.thinBruteBody, Sec2.thinBody] ++ List.replicate 11 .skip ++ procs40
      ++ [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody] ++ R) := by
    simp only [base58, Sec2.programThin, List.append_assoc]
  rw [e]
  exact Sec2.shared_entry std (Sec2.at_prefix rfl _) (Sec2.sharedCallees_of_prefix _ lim std) le_rfl

/-- **The preprocessing at a given place of the memory**, in every program that begins with base58.
-/
theorem preCore_base58 (R : Program) : ∀ lim, PreCoreSpec lim (base58 ++ R) cShared30 :=
  preCoreSpec_all (has40_base58 R) (at_base58 rfl R) (shared_base58 R)








end Light.Sec4

end
end

section


/-!
# Corollaries 26, 31 and 32: the concrete program for given parameters

program31 G = base58 (Theorem 5's and Theorem 30's procedures, numbers 0 to 57) followed by the
procedures 58 to 73 of Section 4.4 (`procs31`): copying, filling, m = ⌈log₄ D⌉, padding and the
inner product; the preprocessing pre31Body G at 64 and the query; their main procedures; the offline
routine and its main procedure; the solver of Corollary 26 for all instances with its test; and the
two procedures for L = ⌈am/b⌉ and t = ⌈pm/q⌉ at 72 and 73. The specifications of the preprocessing,
the query and the offline routine hold for it, for all limits, without hypotheses. At the parameters
of Corollary 26 it is `program26`.

With the two end theorems for light programs and the compiler this gives the two statements about
the word RAM from which Corollaries 26, 31 and 32 follow: on every domain of inputs, and for all
bounds that dominate the two costs of Theorem 30 at the parameters G (`CostsWithin`), the compiled
program is a data structure (`isDataStructure_of_costsWithin`) and solves the offline problem
(`solves_of_costsWithin`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/












/-! ## The program -/










/-- The routines stand at their numbers. -/
theorem program31_at (G : RatParams) (n : ℕ) {body : Stmt} (hn : 58 ≤ n := by norm_num)
    (h : (procs31 G)[n - 58]? = some body := by rfl) : (program31 G)[n]? = some body := by
  rw [program31, List.getElem?_append_right (by rw [length_base58]; exact hn), length_base58]
  exact h

/-- **The preprocessing**, for all limits. -/
theorem pre31_program31_sourceProof (G : RatParams) : ∀ lim, PreSpec31 lim (program31 G) cShared30 G := by
  intro lim N D₀ aX aY fr X Y U μ hin
  have std := hin.lim.std
  have hcopy : CopySpec lim (program31 G) := copy_ok (program31_at G Proc.copy) std
  have hfill : FillSpec lim (program31 G) := fill_ok (program31_at G Proc.fill) std
  have hlog : Log4Spec lim (program31 G) := log4_meets (program31_at G Proc.log4) std
  have hlev : CeilMulSpec lim (program31 G) Proc.levels31 G.a G.b :=
    ceilMul_meets G.hb (program31_at G Proc.levels31)
  have hswi : CeilMulSpec lim (program31 G) Proc.switch31 G.p G.q :=
    ceilMul_meets G.hq (program31_at G Proc.switch31)
  have hpad : PadXSpec lim (program31 G) := padX_meets (program31_at G Proc.padX) hcopy hfill std
  exact pre31_meets G (program31_at G Proc.pre31)
    ⟨hlog, hlev, hswi, hpad, hcopy, hfill, preCore_base58 _ lim⟩ N D₀ aX aY fr X Y U μ hin

























/-! ## The program on the word RAM -/







































end Light.Sec4

end
end


theorem solution : ∀ (G : Light.Sec4.RatParams) (lim : Light.Limits),
  Light.Sec4.PreSpec31 lim (Light.Sec4.program31 G) Light.Sec4.cShared30 G := by
  exact @Light.Sec4.pre31_program31_sourceProof

#print axioms solution
