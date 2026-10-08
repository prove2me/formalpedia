-- Prove2me | solution 1 for Light.Sec3.et17Sizes_spec
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:21:07.628985+00:00
-- url     : https://prove2.me/submissions/419ca237-489a-4be9-95d4-f3fec091e322

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
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_ZOrder
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_APSPSource_ThreeSumApsp_Util_PrimesInWindow
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Common
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSumApsp_Spec_zRow_zCol_quadrant

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




/-- The test a ≤ b holds if and only if a ≤ b. -/
theorem Cond.holds_le {σ : State} {a b : Expr} : ((Light.Cond.le a b)).Holds σ ↔ a.val σ ≤ b.val σ :=
  Int.lt_add_one_iff

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

/-- A branch, followed by the rest of the program: each side, with the rest of the program behind
it, gets the steps that the test leaves. -/
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
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
    Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩










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

theorem SameOn.trans (h₁ : SameOn K μ μ') (h₂ : SameOn K μ' μ'') : SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)

/-- Fewer cells are kept. -/
theorem SameOn.mono (h : SameOn K μ μ') (hK : ∀ b, K' b → K b) : SameOn K' μ μ' :=
  fun b hb => h b (hK b hb)

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














/-! ## The next index -/

/-- The next index, if it is in the same row. -/
theorem succ_div_mod_of_lt {n i : ℕ} (h : i % n + 1 < n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 := by
  have hsucc : i + 1 = i / n * n + (i % n + 1) := by rw [← Nat.add_assoc, Nat.div_add_mod']
  exact ⟨by rw [hsucc, mul_add_div_of_lt h], by rw [hsucc, Nat.mul_add_mod_of_lt h]⟩

/-- The next index, if the test "is this the end of the row?" fails. -/
theorem succ_div_mod_of_ne {n i : ℕ} (hn : 0 < n) (h : i % n + 1 ≠ n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 :=
  succ_div_mod_of_lt (lt_of_le_of_ne (Nat.mod_lt i hn) h)

/-- After the last index of a row comes the first index of the next row. -/
theorem succ_div_mod_of_eq {n i : ℕ} (h : i % n + 1 = n) :
    (i + 1) / n = i / n + 1 ∧ (i + 1) % n = 0 := by
  have hn : 0 < n := h ▸ Nat.succ_pos _
  have hsucc : i + 1 = (i / n + 1) * n + 0 := by
    have hdivmod := Nat.div_add_mod' i n
    rw [Nat.succ_mul]
    -- `i = i / n * n + i % n` and `i % n + 1 = n`
    omega
  exact ⟨by rw [hsucc, mul_add_div_of_lt hn], by rw [hsucc, Nat.mul_add_mod_of_lt hn]⟩

end Nat

namespace Int

/-! ## Residues as natural numbers -/






/-- The residue of an integer modulo `M ≥ 1` is a natural number. -/
theorem natCast_toNat_emod {M : ℕ} (hM : 0 < M) (x : ℤ) : ((x % (M : ℤ)).toNat : ℤ) = x % (M : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg x (Int.natCast_ne_zero_iff_pos.2 hM))

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

/-- Entry `j` of the second of two lists put together. -/
theorem getD_append_add (l l' : List α) (j : ℕ) (d : α) :
    (l ++ l').getD (l.length + j) d = l'.getD j d := by
  rw [List.getD_append_right l l' d _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]


















































/-! ## Blocks one after the other -/

/-- Blocks of any lengths: entry `o` of block `r` stands after the blocks `0, …, r - 1`. -/
theorem getD_flatMap_range_sum (f : ℕ → List α) {n r o : ℕ} (hr : r < n) (ho : o < (f r).length)
    (d : α) :
    ((List.range n).flatMap f).getD (((List.range r).map fun s => (f s).length).sum + o) d =
      (f r).getD o d := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hr
  rw [Nat.add_assoc, List.range_add, List.flatMap_append, ← List.length_flatMap, getD_append_add,
    Nat.add_comm c 1, List.range_add, List.map_append, List.flatMap_append,
    List.getD_append _ _ _ _ (by simpa using ho)]
  simp

/-- The length of `n` blocks of length `k`. -/
theorem length_flatMap_range {k : ℕ} (n : ℕ) (f : ℕ → List α) (hf : ∀ z < n, (f z).length = k) :
    ((List.range n).flatMap f).length = n * k := by
  rw [List.length_flatMap,
    List.map_congr_left (g := fun _ => k) fun z hz => hf z (List.mem_range.1 hz)]
  simp

/-- Blocks of length `k`: entry `r` of block `z` has the index `z * k + r`. -/
theorem getD_flatMap_range {k n : ℕ} (f : ℕ → List α) (hf : ∀ z < n, (f z).length = k) {z r : ℕ}
    (hz : z < n) (hr : r < k) (d : α) :
    ((List.range n).flatMap f).getD (z * k + r) d = (f z).getD r d := by
  rw [← length_flatMap_range z f fun s hs => hf s (hs.trans hz), List.length_flatMap]
  exact getD_flatMap_range_sum f hz (hf z hz ▸ hr) d

















/-- A run of `n` blocks, cut out of a list of blocks of length `k`. -/
theorem take_drop_flatMap_range {k : ℕ} (m n c : ℕ) (f : ℕ → List α)
    (hf : ∀ z < m + n + c, (f z).length = k) :
    (((List.range (m + n + c)).flatMap f).drop (m * k)).take (n * k) =
      (List.range n).flatMap fun z => f (m + z) := by
  have hm : ((List.range m).flatMap f).length = m * k :=
    length_flatMap_range m f fun z hz => hf z (by omega)
  have hn : ((List.range n).flatMap fun z => f (m + z)).length = n * k :=
    length_flatMap_range n _ fun z hz => hf _ (by omega)
  rw [List.range_add, List.range_add, List.flatMap_append, List.flatMap_append, List.append_assoc,
    List.flatMap_map, ← hm, List.drop_left, ← hn, List.take_left]

/-- An entrywise operation on two lists of blocks of one length works block by block. -/
theorem zipWith_flatMap_range {γ : Type*} {k : ℕ} (g : α → β → γ) (n : ℕ) (f : ℕ → List α)
    (f' : ℕ → List β) (hf : ∀ z, (f z).length = k) (hf' : ∀ z, (f' z).length = k) :
    List.zipWith g ((List.range n).flatMap f) ((List.range n).flatMap f') =
      (List.range n).flatMap fun z => List.zipWith g (f z) (f' z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlen : ((List.range n).flatMap f).length = ((List.range n).flatMap f').length := by
      rw [length_flatMap_range n f fun z _ => hf z, length_flatMap_range n f' fun z _ => hf' z]
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_append,
      List.zipWith_append hlen, ih]
    simp








/-! ## Sums -/

/-- The sum of the table `f 0, …, f (n - 1)` is the sum over `Finset.range n`. For a sum over
`Fin n` go on with `Finset.sum_range`. -/
theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  rfl



































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]

/-- The triangle inequality for the sum of a list. -/
theorem abs_sum_le_sum_abs (l : List R) : |l.sum| ≤ (l.map fun x => |x|).sum :=
  Multiset.abs_sum_le_sum_abs (s := (l : Multiset R))

/-- The sum of an initial part of a list is at most the sum of the absolute values of the whole
list, in absolute value. -/
theorem abs_sum_take_le_sum_abs (l : List R) (k : ℕ) :
    |(l.take k).sum| ≤ (l.map fun x => |x|).sum := by
  refine (abs_sum_le_sum_abs _).trans ?_
  refine Sublist.sum_le_sum ((take_sublist k l).map _) fun a ha => ?_
  obtain ⟨x, -, rfl⟩ := mem_map.mp ha
  exact abs_nonneg x

end

/-- If `|f x| ≤ B` for all `x ∈ l`, then every initial part of the numbers `f x` has a sum of
absolute value at most `l.length * B`. -/
theorem abs_sum_take_map_le (l : List α) (f : α → ℤ) {B : ℤ} (h : ∀ x ∈ l, |f x| ≤ B) (k : ℕ) :
    |((l.map f).take k).sum| ≤ l.length * B := by
  refine (List.abs_sum_take_le_sum_abs _ k).trans ?_
  simpa using List.sum_le_card_nsmul ((l.map f).map fun x => |x|) B (by simpa using h)

/-- If `|f x| ≤ B` for all `x ∈ l`, then `|(l.map f).sum| ≤ l.length * B`. -/
theorem abs_sum_map_le (l : List α) (f : α → ℤ) {B : ℤ} (h : ∀ x ∈ l, |f x| ≤ B) :
    |(l.map f).sum| ≤ l.length * B := by
  have htake := abs_sum_take_map_le l f h l.length
  rwa [← List.length_map (f := f), List.take_length, List.length_map] at htake






















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




/-- A bound on the absolute values of all members bounds every entry. -/
theorem AbsLe.getElem {l : List ℤ} {U : ℤ} (h : AbsLe l U) {i : ℕ} (hi : i < l.length) :
    |l[i]| ≤ U :=
  h _ (List.getElem_mem hi)






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

theorem seg_append : Seg μ a (l₁ ++ l₂) ↔ Seg μ a l₁ ∧ Seg μ (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · have := h (l₁.length + i) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi₁ : i < l₁.length
    · rw [List.getElem_append_left hi₁, h₁ i hi₁]
    · have hi₂ : i - l₁.length < l₂.length := by simp at hi; omega
      rw [List.getElem_append_right (by omega), ← h₂ _ hi₂]
      congr 1
      omega

theorem Seg.take (h : Seg μ a l) (k : ℕ) : Seg μ a (l.take k) := fun i hi => by
  have hi' : i < l.length := by simp at hi; omega
  rw [List.getElem_take, h i hi']

theorem Seg.drop (h : Seg μ a l) (k : ℕ) : Seg μ (a + k) (l.drop k) := fun i hi => by
  have hi' : k + i < l.length := by simp at hi; omega
  rw [List.getElem_drop, ← h _ hi', Nat.add_assoc]

/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_52985_0 apspMacro_52985_1);
                                                                                  (first
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_52985_2));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_52985_2 apspMacro_52985_0 (by omega)));
                                                                                                  (revert apspMacro_52985_2)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((simp [] at apspMacro_52985_1);
                                                                                        (((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_52985_3));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_52985_3 apspMacro_52985_0 (by omega)));
                                                                                                  (revert apspMacro_52985_3)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_52985_4));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_52985_4 apspMacro_52985_0 (by omega)));
                                                                                                  (revert apspMacro_52985_4)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (fail
                                                                                            "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                      its condition K x does not follow from the hypotheses."))))) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩

/-- Writing into a segment. -/
theorem Seg.update_in (h : Seg μ a l) {i : ℕ} (hi : i < l.length) (x : ℤ) :
    Seg (Function.update μ (a + i) x) a (l.set i x) := by
  intro j hj
  have hj' : j < l.length := by simpa using hj
  by_cases hji : j = i
  · subst hji; simp
  · rw [Function.update_of_ne (by omega), List.getElem_set_of_ne (by omega), h j hj']

/-- Writing outside a segment. -/
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩





theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl

/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)

/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc

















/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]






/-- Writing just after a segment of natural numbers makes it longer. -/
theorem SegN.snoc {l : List ℕ} (h : SegN μ a l) (x : ℕ) :
    SegN (Function.update μ (a + l.length) (x : ℤ)) a (l ++ [x]) := by
  simpa [SegN] using Seg.snoc h (x : ℤ)












/-- A segment of natural numbers stays where it is if its cells do not change. -/
theorem SegN.keep {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_55152_0 apspMacro_55152_1);
                                                    (first
                                                      |
                                                        ((((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_55152_2));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_55152_2 apspMacro_55152_0 (by omega)));
                                                                    (revert apspMacro_55152_2)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (omega))
                                                      |
                                                        ((simp [] at apspMacro_55152_1);
                                                          (((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_55152_3));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_55152_3 apspMacro_55152_0 (by omega)));
                                                                    (revert apspMacro_55152_3)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (omega))
                                                      |
                                                        ((((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_55152_4));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_55152_4 apspMacro_55152_0 (by omega)));
                                                                    (revert apspMacro_55152_4)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (fail
                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                        its condition K x does not follow from the hypotheses."))))) : SegN μ' a l :=
  Seg.keep h (by simpa using hs)










































end Light

end
end

section


/-!
# Arrays in the memory

A routine assumes the same facts about each of its arrays: which list it holds, how long the list
is, and that it lies below some address `top`, from which on the routine writes: the free pointer,
the place of the result, the scratch space.  `ListAt μ a l N top` is the record of these three
facts, and `ArrayAt μ a l N U top` adds a bound `U` on the entries.  `IndexAt μ a l N p top` is the
record for a list of natural numbers below `p`.  What a routine assumes is then a record with one
field for each array.

* `ListAt.keep`, `ArrayAt.keep`: an array stays in place when its cells do not change.
* `ListAt.mono`, `ArrayAt.mono`: `top` and `U` may grow.
* `ListAt.read`, `ArrayAt.read`, `ArrayAt.abs_read_le`: what a cell holds, and how large it is.
* `ListAt.drop_take`, `ArrayAt.drop_take`: a piece of an array is an array.
* `IndexAt.keep`, `IndexAt.read`, `IndexAt.getD_lt`: the same for natural numbers.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}















namespace ListAt

/-- A list stays in place when its cells do not change.  That they lie below `top` is said again in
the description of the cells: so the promise `Kept μ μ' top` of a callee is enough as it stands. -/
theorem keep (h : ListAt μ a l N top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_56723_0 apspMacro_56723_1);
                                                                    (first
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_56723_2));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_56723_2 apspMacro_56723_0 (by omega)));
                                                                                    (revert apspMacro_56723_2)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((simp [] at apspMacro_56723_1);
                                                                          (((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_56723_3));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_56723_3 apspMacro_56723_0 (by omega)));
                                                                                    (revert apspMacro_56723_3)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_56723_4));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_56723_4 apspMacro_56723_0 (by omega)));
                                                                                    (revert apspMacro_56723_4)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (fail
                                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                        its condition K x does not follow from the hypotheses."))))) : ListAt μ' a l N top :=
  { h with seg := h.seg.congr fun i hi => hs _ (by have := h.len; have := h.below; omega) }

/-- The address `top` may grow. -/
theorem mono (h : ListAt μ a l N top) (ht : top ≤ top' := by first
                                                                | omega
                                                                |
                                                                  (((try have := Light.Std.space_le (by assumption)));
                                                                    ((try have := Light.Std.const_le (by assumption)));
                                                                    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) : ListAt μ a l N top' :=
  { h with below := h.below.trans ht }

/-- Reading a cell. -/
theorem read (h : ListAt μ a l N top) (hi : i < N) : μ (a + i) = l.getD i 0 :=
  h.seg.getD (h.len ▸ hi) 0

/-- The `n` entries from place `k` on. -/
theorem drop_take (h : ListAt μ a l N top) (hk : k + n ≤ N) :
    ListAt μ (a + k) ((l.drop k).take n) n top where
  len := by rw [List.length_take, List.length_drop, h.len]; omega
  seg := (h.seg.drop k).take n
  below := by have := h.below; omega

end ListAt

namespace ArrayAt

/-- An array without the bound on its entries. -/
theorem listAt (h : ArrayAt μ a l N U top) : ListAt μ a l N top := { h with }

/-- An array stays in place when its cells do not change. -/
theorem keep (h : ArrayAt μ a l N U top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_57794_0 apspMacro_57794_1);
                                                                    (first
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_57794_2));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_57794_2 apspMacro_57794_0 (by omega)));
                                                                                    (revert apspMacro_57794_2)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((simp [] at apspMacro_57794_1);
                                                                          (((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_57794_3));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_57794_3 apspMacro_57794_0 (by omega)));
                                                                                    (revert apspMacro_57794_3)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_57794_4));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_57794_4 apspMacro_57794_0 (by omega)));
                                                                                    (revert apspMacro_57794_4)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (fail
                                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                        its condition K x does not follow from the hypotheses."))))) :
    ArrayAt μ' a l N U top :=
  { h with seg := (h.listAt.keep hs).seg }

/-- The bound `U` on the entries and the address `top` may grow. -/
theorem mono (h : ArrayAt μ a l N U top) (hU : U ≤ U' := by first
                                                               | omega
                                                               |
                                                                 (((try have := Light.Std.space_le (by assumption)));
                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (ht : top ≤ top' := by first
                             | omega
                             |
                               (((try have := Light.Std.space_le (by assumption)));
                                 ((try have := Light.Std.const_le (by assumption)));
                                 (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) : ArrayAt μ a l N U' top' :=
  { h with bound := fun x hx => (h.bound x hx).trans hU, below := h.below.trans ht }

/-- Reading a cell. -/
theorem read (h : ArrayAt μ a l N U top) (hi : i < N) : μ (a + i) = l.getD i 0 := h.listAt.read hi

/-- A cell of an array holds a number of absolute value at most `U`. -/
theorem abs_read_le (h : ArrayAt μ a l N U top) (hi : i < N) : |μ (a + i)| ≤ U := by
  rw [h.seg i (h.len ▸ hi)]
  exact h.bound.getElem _

/-- The `n` entries from place `k` on. -/
theorem drop_take (h : ArrayAt μ a l N U top) (hk : k + n ≤ N) :
    ArrayAt μ (a + k) ((l.drop k).take n) n U top :=
  { h.listAt.drop_take hk with
    bound := fun x hx => h.bound x (List.mem_of_mem_drop (List.mem_of_mem_take hx)) }

end ArrayAt









namespace IndexAt

variable {l : List ℕ} {p : ℕ}

/-- A list of natural numbers stays in place when its cells do not change. -/
theorem keep (h : IndexAt μ a l N p top)
    (hs : SameOn (fun b => Inside a N b ∧ b < top) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_59071_0 apspMacro_59071_1);
                                                                    (first
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_59071_2));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_59071_2 apspMacro_59071_0 (by omega)));
                                                                                    (revert apspMacro_59071_2)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((simp [] at apspMacro_59071_1);
                                                                          (((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_59071_3));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_59071_3 apspMacro_59071_0 (by omega)));
                                                                                    (revert apspMacro_59071_3)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_59071_4));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_59071_4 apspMacro_59071_0 (by omega)));
                                                                                    (revert apspMacro_59071_4)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (fail
                                                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                        its condition K x does not follow from the hypotheses."))))) :
    IndexAt μ' a l N p top :=
  { h with
    seg := Seg.congr h.seg fun i hi => hs _ (by
      have := h.len
      have := h.below
      rw [List.length_map] at hi
      omega) }

/-- Reading a cell. -/
theorem read (h : IndexAt μ a l N p top) (hi : i < N) : μ (a + i) = (l.getD i 0 : ℕ) :=
  h.seg.read (h.len ▸ hi)

/-- An entry is below `p`. -/
theorem getD_lt (h : IndexAt μ a l N p top) (hi : i < N) : l.getD i 0 < p := by
  have hl : i < l.length := h.len ▸ hi
  rw [List.getD_eq_getElem _ 0 hl]
  exact h.lt _ (List.getElem_mem hl)

end IndexAt

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
    ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by ((try refine Light.SameOn.cell ?_); (intro apspMacro_63531_0 apspMacro_63531_1);
                                                                                   (first
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_63531_2));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_63531_2 apspMacro_63531_0 (by omega)));
                                                                                                   (revert apspMacro_63531_2)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((simp [] at apspMacro_63531_1);
                                                                                         (((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_63531_3));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_63531_3 apspMacro_63531_0 (by omega)));
                                                                                                   (revert apspMacro_63531_3)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_63531_4));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_63531_4 apspMacro_63531_0 (by omega)));
                                                                                                   (revert apspMacro_63531_4)));
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
# From a pair to the next pair

A loop that runs through the pairs (a, b) with a, b < n in the order of their numbers t = a n + b
keeps a = t / n and b = t % n in two local variables, so that no division is needed.
`nextPair A B N` is the step from one pair to the next, and `Ends.nextPair` is its rule.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}





/-- **From the pair number t to the pair number t + 1.** -/
theorem Ends.nextPair {A B N n t T : ℕ} {l : List ℤ} {μ : ℕ → ℤ} {Q : State → Prop}
    (h : Q ⟨frame (setLocal (setLocal l B ((t + 1) % n : ℕ)) A ((t + 1) / n : ℕ)), μ⟩)
    (hn : 0 < n) (ht : ((t + 1 : ℕ) : ℤ) ≤ lim.word) (hnw : (n : ℤ) ≤ lim.word)
    (hA : frame l A = (t / n : ℕ)) (hB : frame l B = (t % n : ℕ)) (hN : frame l N = n)
    (hAB : A ≠ B := by decide) (hBN : N ≠ B := by decide) (hT : 14 ≤ T := by first
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
    Ends lim P d (nextPair A B N) ⟨frame l, μ⟩ T Q := by
  have hmod := Nat.mod_lt t hn
  have hdiv := Nat.div_le_self t n
  have hlast := Nat.succ_div_mod_of_eq (n := n) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (i := t) hn
  generalize t / n = a at *
  generalize t % n = b at *
  -- b := b + 1
  refine Ends.setToThen (b + 1 : ℕ) ?_ (by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                                               Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                                               reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                                               Nat.cast_zero, Nat.cast_one, Expr.Gives, hB, abs_le]; omega)
    (by simp; omega)
  -- if b = n then b := 0; a := a + 1
  refine Ends.iteLast (fun he => ?_) (fun he => ?_) ⟨trivial, trivial⟩ (by simp; omega)
  · have he : b + 1 = n := by
      have : ((b + 1 : ℕ) : ℤ) = n := by
        simpa only [Cond.Holds, Expr.val, frame_setLocal, if_pos, if_neg hBN, hN] using he
      exact_mod_cast this
    rw [(hlast he).1, (hlast he).2] at h
    refine Ends.setToThen (0 : ℕ) (Ends.setTo (a + 1 : ℕ) ?_
      (by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
            Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
            reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
            Nat.cast_zero, Nat.cast_one, Expr.Gives, frame_setLocal, if_neg hAB, hA,
            abs_le]; omega)
      (by simp; omega)) (by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                              Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                              reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                              Nat.cast_zero, Nat.cast_one, Expr.Gives]; omega) (by simp; omega)
    convert h using 2
    funext y
    simp only [frame_setLocal]
    split_ifs <;> rfl
  · have he : b + 1 ≠ n := fun e => he (by
      simp only [Cond.Holds, Expr.val, frame_setLocal, if_pos, if_neg hBN, hN]
      exact_mod_cast e)
    rw [(hinner he).1, (hinner he).2] at h
    refine Ends.skip ?_
    convert h using 2
    funext y
    simp only [frame_setLocal]
    split_ifs with h1 h2 h2
    · exact absurd (h2.symm.trans h1) hAB
    · rfl
    · rw [h2, hA]
    · rfl

end Light

end
end

section


/-!
# The sieve of Eratosthenes

sieve(m, out, fr) writes the primes up to m in ascending order to the cells from out and returns
their number (`sieve_meets`).  It uses a table of m + 1 cells at the free pointer fr, about which
nothing is assumed.

* The table is cleared (`clear_ends`).
* The candidates i = 2, …, m are tried in turn (`round_ends`).  Before the round for i, cell fr + j
  holds 0 unless j is a proper multiple of a prime below i (`Sieved`, `Marked`); so i is a prime if
  and only if cell fr + i holds 0 (`prime_iff_not_marked`).
* A prime is appended to the list, and its proper multiples are marked (`take_ends`, `mark_ends`).

The number of steps, `sieveTime m`, is of the order m log m: a prime i costs m / i rounds of
marking, and the sum of m / i over all i ≤ m is at most m (⌊log₂ m⌋ + 1) (`sum_div_le`, `time_le`).

Everything but `sieveBody`, `sieveTime` and `sieve_meets` is in the namespace `Sieve`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Sieve

/-! ## The pure side -/




theorem primesBelow_two : primesBelow 2 = [] := by decide

theorem primesBelow_one : primesBelow 1 = [] := by decide

theorem primesBelow_succ_of_prime {c : ℕ} (h : c.Prime) :
    primesBelow (c + 1) = primesBelow c ++ [c] := by
  simp [primesBelow, List.range_succ, List.filter_append, h]

theorem primesBelow_succ_of_not_prime {c : ℕ} (h : ¬ c.Prime) :
    primesBelow (c + 1) = primesBelow c := by
  simp [primesBelow, List.range_succ, List.filter_append, h]

/-- There are at most i - 2 primes below i. -/
theorem length_primesBelow_add_two_le {i : ℕ} (hi : 2 ≤ i) : (primesBelow i).length + 2 ≤ i := by
  induction i, hi using Nat.le_induction with
  | base => simp [primesBelow_two]
  | succ i _ ih =>
    by_cases h : i.Prime
    · rw [primesBelow_succ_of_prime h]
      simpa using ih
    · rw [primesBelow_succ_of_not_prime h]
      omega

/-- The list is the sorted list of the set of primes up to m. -/
theorem sort_primesLE (m : ℕ) : (Nat.primesLE m).sort (· ≤ ·) = primesBelow (m + 1) := by
  refine List.Perm.eq_of_pairwise' (Finset.pairwise_sort _ _) ?_ ?_
  · exact (List.pairwise_le_range).filter _
  · refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (List.nodup_range.filter _)).2
      fun q => ?_
    simp [Nat.mem_primesLE]

theorem length_primesBelow (m : ℕ) : (primesBelow (m + 1)).length = (Nat.primesLE m).card := by
  rw [← sort_primesLE, Finset.length_sort]




theorem not_marked_two (j : ℕ) : ¬ Marked 2 j := by
  rintro ⟨p, hp, h2, -, -⟩
  exact absurd hp.two_le (by omega)

/-- A number from 2 on is prime if and only if it is not a proper multiple of a smaller prime. -/
theorem prime_iff_not_marked {i : ℕ} (hi : 2 ≤ i) : i.Prime ↔ ¬ Marked i i := by
  constructor
  · rintro h ⟨p, hp, hlt, hdvd, -⟩
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp h).1 hdvd) (by omega)
  · intro h
    by_contra hn
    have hlt := (Nat.not_prime_iff_minFac_lt hi).1 hn
    exact h ⟨i.minFac, Nat.minFac_prime (by omega), hlt, Nat.minFac_dvd i, hlt⟩

theorem marked_succ_of_not_prime {i : ℕ} (h : ¬ i.Prime) (j : ℕ) :
    Marked (i + 1) j ↔ Marked i j := by
  constructor
  · rintro ⟨p, hp, hlt, h1, h2⟩
    have : p ≠ i := by
      rintro rfl
      exact h hp
    exact ⟨p, hp, by omega, h1, h2⟩
  · rintro ⟨p, hp, hlt, h1, h2⟩
    exact ⟨p, hp, by omega, h1, h2⟩

theorem marked_succ_of_prime {i : ℕ} (h : i.Prime) (j : ℕ) :
    Marked (i + 1) j ↔ Marked i j ∨ (i ∣ j ∧ i < j) := by
  constructor
  · rintro ⟨p, hp, hlt, h1, h2⟩
    by_cases hpi : p = i
    · subst hpi
      exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨p, hp, by omega, h1, h2⟩
  · rintro (⟨p, hp, hlt, h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨p, hp, by omega, h1, h2⟩
    · exact ⟨i, h, by omega, h1, h2⟩

/-- The sum of m / i over 1 ≤ i < 2^k is at most k m. -/
theorem sum_div_pow_le (m k : ℕ) : ∑ r ∈ Finset.range (2 ^ k - 1), m / (r + 1) ≤ k * m := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 2 ^ k := by
      have := Nat.one_le_two_pow (n := k)
      rw [pow_succ]
      omega
    rw [h2, Finset.sum_range_add]
    have hblock : ∑ x ∈ Finset.range (2 ^ k), m / (2 ^ k - 1 + x + 1) ≤ m := by
      calc ∑ x ∈ Finset.range (2 ^ k), m / (2 ^ k - 1 + x + 1)
          ≤ ∑ _x ∈ Finset.range (2 ^ k), m / 2 ^ k := by
            refine Finset.sum_le_sum fun x _ => Nat.div_le_div_left ?_ (by positivity)
            have := Nat.one_le_two_pow (n := k)
            omega
        _ = 2 ^ k * (m / 2 ^ k) := by simp
        _ ≤ m := Nat.mul_div_le m _
    have : (k + 1) * m = k * m + m := by ring
    omega

/-- The sum of m / i over 2 ≤ i ≤ m is at most m (⌊log₂ m⌋ + 1). -/
theorem sum_div_le (m : ℕ) : ∑ r ∈ Finset.range (m - 1), m / (r + 2) ≤ (Nat.log 2 m + 1) * m := by
  have h1 : ∑ r ∈ Finset.range (m - 1), m / (r + 2)
      ≤ ∑ r ∈ Finset.range (m - 1 + 1), m / (r + 1) := by
    rw [Finset.sum_range_succ']
    exact Nat.le_add_right _ _
  have h2 : ∑ r ∈ Finset.range (m - 1 + 1), m / (r + 1)
      ≤ ∑ r ∈ Finset.range (2 ^ (Nat.log 2 m + 1) - 1), m / (r + 1) := by
    refine Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 ?_)
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    have h3 : 2 ≤ 2 ^ (Nat.log 2 m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Nat.log 2 m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [Nat.succ_eq_add_one] at this
    omega
  exact h1.trans (h2.trans (sum_div_pow_le m _))

/-! ## The program -/














































variable {μ : ℕ → ℤ} {m out fr : ℕ}













/-- Clearing the table, two assignments, the main loop and the last assignment. -/
theorem time_le (m : ℕ) : 15 * m + 23 + 4 + loopTime m + 2 ≤ sieveTime m := by
  have hsum := sum_div_le m
  have hmul : 15 * m * (Nat.log 2 m + 5) = 15 * ((Nat.log 2 m + 1) * m) + 60 * m := by ring
  simp only [loopTime, sieveTime, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, ← Finset.mul_sum]
  omega






/-- The table is cleared. -/
theorem clear_ends (pre : Pre lim m out fr) :
    Ends lim P d clear ⟨frame [m, out, fr], μ⟩ (15 * m + 23) (Cleared μ m out fr (m + 1)) := by
  (obtain ⟨⟩ := id pre)
  -- i := 0
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
          (0 : ℕ)
            -- while i ≤ m
            
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
  -- while i ≤ m
  refine Ends.whileBlock (Cleared μ m out fr) (m + 1) ?start ?round ?done
  case start => exact ⟨μ, rfl, fun i hi => absurd hi (by omega), .refl⟩
  case done =>
    rintro _ ⟨μ', rfl, hzero, same⟩
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), μ', rfl, hzero, same⟩
  case round =>
    rintro j _ hj ⟨μ', rfl, hzero, same⟩
    -- table[i] := 0; i := i + 1
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), Function.update μ' (fr + j) 0, ?_, ?_,
      same.update ⟨by omega, by omega⟩ _⟩
    · simp [update_frame_setLocal]
    · intro i hi
      by_cases h : i = j
      · simp [h]
      · rw [Function.update_of_ne (by omega)]
        exact hzero i (by omega)

/-- Among the multiples of i, those below J + i are those below J, and J itself. -/
theorem lt_add_iff_of_dvd {i j J : ℕ} (hJ : i ∣ J) (hj : i ∣ j) (hne : j ≠ J) : j < J + i ↔ j < J :=
  ⟨fun h => lt_of_le_of_ne (Nat.le_of_lt_add_of_dvd h hj hJ) hne, fun h => by omega⟩








/-- table[J] := 1; J := J + i. -/
theorem mark_round {i cnt J : ℕ} {σ : State} (pre : Pre lim m out fr) (hi : 1 ≤ i) (hJ : i ∣ J)
    (hiJ : i < J) (hJm : J ≤ m) (h : Marking μ m out fr i cnt J σ) :
    ((Light.Stmt.seq
       (Stmt.store ((Light.Expr.op Light.Op.add) (v Table) (v Mult)) (k 1))
       (.set Mult ((Light.Expr.op Light.Op.add) (v Mult) (v Cand))))).Runs lim σ
      (Marking μ m out fr i cnt (J + i)) := by
  (obtain ⟨⟩ := id pre)
  obtain ⟨μ', rfl, htab, same⟩ := h
  refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                 ((try have := Light.Std.const_le (by assumption)));
                 (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), Function.update μ' (fr + J) 1, by simp [update_frame_setLocal], ?_,
    same.update ⟨by omega, by omega⟩ _⟩
  intro j hj
  by_cases hjJ : j = J
  · subst hjJ
    rw [Function.update_self, if_pos ⟨hJ, hiJ, by omega⟩]
  · rw [Function.update_of_ne (by omega), htab j hj]
    by_cases hdvd : i ∣ j
    · simp only [hdvd, true_and, lt_add_iff_of_dvd hJ hdvd hjJ]
    · simp only [hdvd, false_and]

/-- The proper multiples of i are marked, in m / i - 1 rounds. -/
theorem mark_ends {i cnt : ℕ} (pre : Pre lim m out fr) (hi : 1 ≤ i) (him : i ≤ m) :
    Ends lim P d mark ⟨frame [m, out, fr, i, (2 * i : ℕ), cnt], μ⟩ (15 * (m / i) + 6) fun σ' =>
      ∃ J, m < J ∧ Marking μ m out fr i cnt J σ' := by
  (obtain ⟨⟩ := id pre)
  have hq : 1 ≤ m / i := (Nat.le_div_iff_mul_le hi).2 (by omega)
  -- while J ≤ m
  refine Ends.whileBlock (fun t => Marking μ m out fr i cnt ((t + 2) * i)) (m / i - 1) ?start ?round
    ?done (by first
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
  case start =>
    refine ⟨μ, by simp, fun j _ => (if_neg ?_).symm, .refl⟩
    rintro ⟨hdvd, hlt, hlt2⟩
    exact absurd (Nat.le_of_lt_add_of_dvd (by omega : j < i + i) hdvd dvd_rfl) (by omega)
  case done =>
    rintro _ h
    have hgt : m < (m / i - 1 + 2) * i := by
      rw [show m / i - 1 + 2 = m / i + 1 by omega]
      exact (Nat.div_lt_iff_lt_mul hi).1 (Nat.lt_succ_self _)
    generalize (m / i - 1 + 2) * i = J at h hgt
    obtain ⟨μ', rfl, -⟩ := id h
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), J, hgt, h⟩
  case round =>
    rintro t σ ht h
    have hle : (t + 2) * i ≤ m := (Nat.le_div_iff_mul_le hi).1 (by omega)
    have hlt : i < (t + 2) * i :=
      lt_of_lt_of_le (by omega : i < 2 * i) (Nat.mul_le_mul_right i (by omega))
    have hrun := mark_round pre hi (Dvd.intro_left _ rfl) hlt hle h
    rw [show (t + 2) * i + i = (t + 1 + 2) * i by ring] at hrun
    generalize (t + 2) * i = J at h hle
    obtain ⟨μ', rfl, -⟩ := h
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hrun⟩










/-- A prime candidate is written to the list, and its proper multiples are marked. -/
theorem take_ends {i : ℕ} {σ : State} (pre : Pre lim m out fr) (him : i ≤ m) (hprime : i.Prime)
    (h : Sieved μ m out fr i i σ) :
    Ends lim P d take σ (15 * (m / i) + 19) (Sieved μ m out fr i (i + 1)) := by
  (obtain ⟨⟩ := id pre)
  obtain ⟨μ', J, rfl, seg, htab, kept⟩ := h
  have hcnt := length_primesBelow_add_two_le hprime.two_le
  -- out[cnt] := i
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen (out + (primesBelow i).length) i ?_ ?_ ?_);
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
  -- cnt := cnt + 1
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
          ((primesBelow i).length + 1 : ℕ)
            -- J := i + i
            
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
  -- J := i + i
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
          (2 * i : ℕ)
            -- the proper multiples of i
            
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
  -- the proper multiples of i
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (mark_ends pre hprime.one_le him) ?_ ?_
      | refine Light.Ends.pieceLast (mark_ends pre hprime.one_le him) ?_ ?_);
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
    (on_goal -1 => rintro _ ⟨J', hJ', μ'', rfl, htab', same⟩)
  rw [Sieved, primesBelow_succ_of_prime hprime]
  refine ⟨μ'', J', by simp,
    (seg.snoc i).keep (SameOn.mono same fun b hb => Or.inl (by simp at hb; omega)), fun j hj => ?_,
    (kept.write (by omega) _).then same fun b hb => ⟨hb, hb.2⟩⟩
  rw [htab' j hj, Function.update_of_ne (by omega), marked_succ_of_prime hprime]
  by_cases hmul : i ∣ j ∧ i < j
  · simp [hmul, show j < J' by omega]
  · have : ¬ (i ∣ j ∧ i < j ∧ j < J') := fun hc => hmul ⟨hc.1, hc.2.1⟩
    rw [if_neg this, htab j hj]
    tauto

/-- i := i + 1. -/
theorem next_ends {i T : ℕ} {σ : State} (pre : Pre lim m out fr) (him : i ≤ m)
    (h : Sieved μ m out fr i (i + 1) σ) (hT : 4 ≤ T) :
    Ends lim P d (.set Cand (((Light.Expr.op Light.Op.add) (v Cand) (k 1)))) σ T (Sieved μ m out fr (i + 1) (i + 1)) := by
  (obtain ⟨⟩ := id pre)
  obtain ⟨μ', J, rfl, hrest⟩ := h
  exact Ends.setTo (i + 1 : ℕ) ⟨μ', J, rfl, hrest⟩

/-- One round of the main loop: the candidate i is dealt with, and the next candidate is i + 1. -/
theorem round_ends {i : ℕ} {σ : State} (pre : Pre lim m out fr) (hi : 2 ≤ i) (him : i ≤ m)
    (h : Sieved μ m out fr i i σ) :
    Ends lim P d round σ (15 * (m / i) + 30) (Sieved μ m out fr (i + 1) (i + 1)) := by
  (obtain ⟨⟩ := id pre)
  have htake := fun hprime => take_ends (P := P) (d := d) pre him hprime h
  obtain ⟨μ', J, rfl, seg, htab, kept⟩ := h
  -- if table[i] = 0
  refine Ends.iteThen (fun hc => ?_) fun hc => ?_
  · have hzero : μ' (fr + i) = 0 := by simpa using hc
    have hprime : i.Prime := (prime_iff_not_marked hi).2 ((htab i him).1 hzero)
    exact Ends.next _
      ((htake hprime).mono le_rfl fun _ h' => next_ends pre him h' (by first
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
                                                                             | ((ring_nf); (omega)))))
  · have hzero : μ' (fr + i) ≠ 0 := by simpa using hc
    have hprime : ¬ i.Prime := fun hp => hzero ((htab i him).2 ((prime_iff_not_marked hi).1 hp))
    refine Ends.next 0 (Ends.skip (next_ends pre him ?_ (by first
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
                                                                  | ((ring_nf); (omega))))))
    rw [Sieved, primesBelow_succ_of_not_prime hprime]
    exact ⟨μ', J, rfl, seg,
      fun j hj => (htab j hj).trans (marked_succ_of_not_prime hprime j).not.symm, kept⟩

/-- **sieve(m, out, fr)** writes the primes up to m in ascending order to out and returns their
number.  Only the m cells from out and the m + 1 cells from fr may change. -/
theorem _root_.Light.sieve_meets {p : ℕ} (hp : P[p]? = some sieveBody) (pre : Pre lim m out fr) :
    Meets lim P p d [m, out, fr] μ (sieveTime m) fun r μ' =>
      r = ((Nat.primesLE m).card : ℤ) ∧ SegN μ' out ((Nat.primesLE m).sort (· ≤ ·)) ∧
        SameOutside2 μ μ' out m fr (m + 1) := by
  (obtain ⟨⟩ := id pre)
  have htime := time_le m
  refine .of_body hp ?_
  -- the table is cleared
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (clear_ends pre) ?_ ?_
      | refine Light.Ends.pieceLast (clear_ends pre) ?_ ?_);
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
        rintro _
          ⟨μ₁, rfl, hzero, same⟩
              -- i := 2; cnt := 0
              )
  -- i := 2; cnt := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (2 : ℕ) ?_ ?_ ?_);
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
          (0 : ℕ)
            -- while i ≤ m
            
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
  -- while i ≤ m
  refine Ends.next (loopTime m) ((Ends.while (fun r => Sieved μ m out fr (r + 2) (r + 2)) (m - 1)
    (fun r => 15 * (m / (r + 2)) + 30) ?start ?round ?done).mono (le_of_eq (by simp [loopTime]))
    fun _ h => h)
  case start =>
    rw [Sieved, primesBelow_two]
    exact ⟨μ₁, 0, rfl, Seg.nil, fun j hj => by simp [hzero j (by omega), not_marked_two],
      SameOn.mono same fun b hb => hb.2⟩
  case round =>
    rintro r σ hr h
    have hrun := round_ends (P := P) (d := d) pre (by omega) (by omega : r + 2 ≤ m) h
    obtain ⟨μ', J, rfl, -⟩ := h
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hrun⟩
  case done =>
    rintro _ ⟨μ', J, rfl, seg, -, kept⟩
    have hlist : primesBelow (m - 1 + 2) = primesBelow (m + 1) := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · rw [primesBelow_two, primesBelow_one]
      · rw [show m - 1 + 2 = m + 1 by omega]
    rw [hlist] at seg
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- the result is cnt
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen ((primesBelow (m + 1)).length : ℕ) ?_ ?_ ?_);
      (on_goal -1 =>
          first
          |
            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlist]);
              (first
                | omega
                | ((ring_nf); (omega))))
          | omega
          |
            (simp [hlist] <;>
                first
                | omega
                | ((ring_nf); (omega))));
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hlist] <;> omega)));
      (try with_unfolding_none refine Light.Ends.skip ?_)
    refine ⟨?_, ?_, kept⟩
    · simp [length_primesBelow]
    · rw [sort_primesLE]
      exact seg

end Sieve

end Light

end
end

section


/-!
# The integer square root by counting up

sqrt(K) returns ⌊√K⌋ within `sqrtTime K` steps (`sqrt_meets`), by running through the squares 1, 4,
9, …: after (k + 1)² comes (k + 1)² + 2k + 3.  It does not touch the memory.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Sqrt







end Sqrt














/-- **sqrt(K)** returns ⌊√K⌋ and leaves the memory as it is. -/
theorem sqrt_meets {p K : ℕ} (hp : P[p]? = some sqrtBody) (μ : ℕ → ℤ)
    (hword : ((3 * K + 4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [K] μ (sqrtTime K) fun r μ' => r = (Nat.sqrt K : ℤ) ∧ μ' = μ := by
  have hle : Nat.sqrt K * Nat.sqrt K ≤ K := Nat.sqrt_le K
  have hlt : K < (Nat.sqrt K + 1) * (Nat.sqrt K + 1) := Nat.lt_succ_sqrt K
  have hself : Nat.sqrt K ≤ K := Nat.sqrt_le_self K
  refine .of_body hp ?_
  unfold sqrtBody sqrtTime
  -- k := 0; sq := 1
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
          1
            -- while sq ≤ K.  Before round i, k = i and sq = (i + 1)².
            
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
  -- while sq ≤ K.  Before round i, k = i and sq = (i + 1)².
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [K, i, ((i + 1) * (i + 1) : ℕ)], μ⟩) (Nat.sqrt K) (by simp) ?round ?done
    le_rfl)
  case round =>
    rintro i _ hi rfl
    have hsq : (i + 1) * (i + 1) ≤ Nat.sqrt K * Nat.sqrt K := Nat.mul_le_mul (by omega) (by omega)
    rw [show (i + 1 + 1) * (i + 1 + 1) = (i + 1) * (i + 1) + 2 * i + 3 by ring]
    generalize (i + 1) * (i + 1) = q at hsq
    -- The test is safe and holds.  sq := sq + 2 k + 3; k := k + 1 is safe and leads to the next
    -- state.
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    generalize (Nat.sqrt K + 1) * (Nat.sqrt K + 1) = q at hlt
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- the result is k
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (Nat.sqrt K) ?_ ?_ ?_);
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

end Light

end
end

section


/-!
# Matrices in Z-order (Morton order)

The count of the proof of Theorem 17 needs a product of matrices over `ℤ[x]/(x^p - 1)`, "O(n^{log₂
7}) with Strassen's algorithm".  For the recursion of that algorithm a `2^K × 2^K` matrix is stored
in Z-order: the entry `(a, c)` stands at the place whose digits in base 4 are `2 a_i + c_i`, where
`a_i` and `c_i` are the binary digits of `a` and `c`.

* Places: `zIdx` maps a pair to its place, `zRow` and `zCol` map back (`zRow_zIdx`, `zCol_zIdx`,
  `zIdx_zRow_zCol`).  All three are computed one digit in base 4 at a time (`zIdx_eq`, `zRow_eq`,
  `zCol_eq`), and every proof is an induction along these equations.
* Lists: the entry `(a, c)` of `zList K M` starts at `zIdx a c * p` (`getD_zList`).
* **The four quadrants of a matrix are the four quarters of its list** (`quarter_zList`,
  `zList_succ`), which is what the recursion needs.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Places -/

















/-- The last binary digit goes to the last digit in base 4. -/
theorem spread_eq (i : ℕ) : spread i = i % 2 + 4 * spread (i / 2) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [spread]
  · unfold spread
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hi.ne', Nat.ofDigits_cons]

/-- The number 0 has no digits to move. -/
theorem spread_zero : spread 0 = 0 := by simp [spread]

/-- The row, one digit in base 4 at a time. -/
theorem zRow_eq (z : ℕ) : zRow z = z % 4 / 2 + 2 * zRow (z / 4) := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp [zRow]
  · unfold zRow
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hz.ne', List.map_cons, Nat.ofDigits_cons]

/-- The column, one digit in base 4 at a time. -/
theorem zCol_eq (z : ℕ) : zCol z = z % 4 % 2 + 2 * zCol (z / 4) := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp [zCol]
  · unfold zCol
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hz.ne', List.map_cons, Nat.ofDigits_cons]

/-- The place 0 is in row 0. -/
theorem zRow_zero : zRow 0 = 0 := by simp [zRow]

/-- The place 0 is in column 0. -/
theorem zCol_zero : zCol 0 = 0 := by simp [zCol]

/-- The place, one digit in base 4 at a time. -/
theorem zIdx_eq (a c : ℕ) : zIdx a c = (2 * (a % 2) + c % 2) + 4 * zIdx (a / 2) (c / 2) := by
  unfold zIdx
  rw [spread_eq a, spread_eq c]
  ring

/-- The places of a `2^K × 2^K` matrix are below `4^K`. -/
theorem zIdx_lt {K a c : ℕ} (ha : a < 2 ^ K) (hc : c < 2 ^ K) : zIdx a c < 4 ^ K := by
  induction K generalizing a c with
  | zero =>
    obtain rfl : a = 0 := by simpa using ha
    obtain rfl : c = 0 := by simpa using hc
    simp [zIdx, spread_zero]
  | succ K ih =>
    rw [pow_succ] at ha hc
    have h := ih (a := a / 2) (c := c / 2) (by omega) (by omega)
    rw [zIdx_eq, pow_succ]
    omega

/-- The row and the column of the place of `(a, c)` are `a` and `c`. -/
private theorem zRow_zCol_zIdx (a c : ℕ) : zRow (zIdx a c) = a ∧ zCol (zIdx a c) = c := by
  induction hm : a + c using Nat.strong_induction_on generalizing a c with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos (a + c) with h0 | hpos
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := by omega
      simp [zIdx, spread_zero, zRow_zero, zCol_zero]
    · obtain ⟨hrow, hcol⟩ := ih (a / 2 + c / 2) (by omega) (a / 2) (c / 2) rfl
      rw [zRow_eq, zCol_eq, zIdx_eq]
      generalize zIdx (a / 2) (c / 2) = z at hrow hcol
      rw [show (2 * (a % 2) + c % 2 + 4 * z) / 4 = z by omega, hrow, hcol]
      omega

/-- The row of the place of `(a, c)` is `a`. -/
theorem zRow_zIdx (a c : ℕ) : zRow (zIdx a c) = a := (zRow_zCol_zIdx a c).1

/-- The column of the place of `(a, c)` is `c`. -/
theorem zCol_zIdx (a c : ℕ) : zCol (zIdx a c) = c := (zRow_zCol_zIdx a c).2

/-- A place is the place of its row and its column. -/
theorem zIdx_zRow_zCol (z : ℕ) : zIdx (zRow z) (zCol z) = z := by
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · simp [zRow_zero, zCol_zero, zIdx, spread_zero]
    · have h := ih (z / 4) (by omega)
      rw [zIdx_eq, zRow_eq z, zCol_eq z]
      generalize zRow (z / 4) = a at h
      generalize zCol (z / 4) = c at h
      rw [show (z % 4 / 2 + 2 * a) / 2 = a by omega, show (z % 4 % 2 + 2 * c) / 2 = c by omega, h]
      omega




















/-! ## Matrices as lists -/








/-- A matrix of vectors of length `p` has `4^K p` numbers. -/
theorem length_zList {p : ℕ} (K : ℕ) (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p) :
    (zList K M).length = 4 ^ K * p :=
  List.length_flatMap_range _ _ fun _ _ => hM _ _

/-- The entry `(a, c)` of the matrix stands at the place `zIdx a c`. -/
theorem getD_zList {p K a c r : ℕ} (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p)
    (ha : a < 2 ^ K) (hc : c < 2 ^ K) (hr : r < p) :
    (zList K M).getD (zIdx a c * p + r) 0 = (M a c).getD r 0 := by
  rw [zList, List.getD_flatMap_range _ (fun _ _ => hM _ _) (zIdx_lt ha hc) hr, zRow_zIdx, zCol_zIdx]

/-- **The quadrants of a matrix are the quarters of its list.** -/
theorem quarter_zList {p K t : ℕ} (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p)
    (ht : t < 4) :
    quarter (4 ^ K * p) t (zList (K + 1) M) =
      zList K fun a c => M (a + t / 2 * 2 ^ K) (c + t % 2 * 2 ^ K) := by
  have hsplit : 4 ^ (K + 1) = t * 4 ^ K + 4 ^ K + (3 - t) * 4 ^ K := by
    calc 4 ^ (K + 1) = (t + 1 + (3 - t)) * 4 ^ K := by
          rw [show t + 1 + (3 - t) = 4 by omega, pow_succ, Nat.mul_comm]
      _ = _ := by ring
  rw [quarter, zList, hsplit, ← Nat.mul_assoc,
    List.take_drop_flatMap_range _ _ _ _ fun _ _ => hM _ _,
    zList]
  refine List.flatMap_congr fun z hz => ?_
  obtain ⟨hrow, hcol⟩ := zRow_zCol_quadrant ht (List.mem_range.1 hz)
  rw [hrow, hcol]

/-- A list of length `4 q` is put together from its four quarters. -/
private theorem eq_append_quarters {q : ℕ} {l : List ℤ} (hl : l.length = 4 * q) :
    l = quarter q 0 l ++ quarter q 1 l ++ quarter q 2 l ++ quarter q 3 l := by
  unfold quarter
  refine List.ext_getElem (by simp; omega) fun i _ _ => ?_
  simp only [List.getElem_append, List.length_append, List.length_take, List.length_drop,
    List.getElem_take, List.getElem_drop]
  split_ifs <;> congr 1 <;> omega

/-- A matrix is put together from its four quadrants. -/
theorem zList_succ {p K : ℕ} (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, (M a c).length = p) :
    zList (K + 1) M = zList K (fun a c => M a c) ++ zList K (fun a c => M a (c + 2 ^ K)) ++
      zList K (fun a c => M (a + 2 ^ K) c) ++ zList K fun a c => M (a + 2 ^ K) (c + 2 ^ K) := by
  have hlen : (zList (K + 1) M).length = 4 * (4 ^ K * p) := by
    rw [length_zList _ _ hM, pow_succ]
    ring
  conv_lhs => rw [eq_append_quarters hlen]
  rw [quarter_zList M hM (by norm_num), quarter_zList M hM (by norm_num),
    quarter_zList M hM (by norm_num), quarter_zList M hM (by norm_num)]
  simp only [Nat.reduceDiv, Nat.reduceMod, Nat.zero_mul, Nat.one_mul, Nat.add_zero]

end ThreeSumApsp.Spec

end
end

section


/-!
# The table of `spread`: small facts

`spread i` is the number whose digits in base 4 are the binary digits of i; the place of the entry
(a, c) of a matrix in Z-order is 2 spread a + spread c.  The routines that write matrices in Z-order
and the routine that reads the count off their product look `spread` up in a table,
`spreadList n`, the list of spread 0, …, spread (n - 1).  Here are the facts on the table that both
use: a bound on its entries, how it grows, and what a cell of it holds.
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The number whose digits in base 4 are the binary digits of i is at most i². -/
theorem spread_le_sq (i : ℕ) : spread i ≤ i * i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [spread_zero]
    · have h := ih (i / 2) (by omega)
      rw [spread_eq]
      obtain ⟨q, b, hb, rfl⟩ : ∃ q b, b < 2 ∧ i = 2 * q + b :=
        ⟨i / 2, i % 2, Nat.mod_lt _ (by norm_num), by omega⟩
      rw [show (2 * q + b) / 2 = q by omega] at h ⊢
      rw [show (2 * q + b) % 2 = b by omega]
      nlinarith

theorem spreadList_succ (i : ℕ) : spreadList (i + 1) = spreadList i ++ [((spread i : ℕ) : ℤ)] := by
  simp [spreadList, List.range_succ]

theorem length_spreadList (i : ℕ) : (spreadList i).length = i := by simp [spreadList]

/-- A cell of the table. -/
theorem seg_spreadList_get {μ : ℕ → ℤ} {a n i : ℕ} (h : Seg μ a (spreadList n)) (hi : i < n) :
    μ (a + i) = (spread i : ℕ) := by
  have := h i (by rw [length_spreadList]; exact hi)
  simpa [spreadList] using this

end Light.Sec3

end
end

section


/-!
# The problems of the paper as tasks

* The problems for Section 3.4 have a size and a bound (`Task`).
* The problems of Theorem 5 and of Section 3.1 have the parameters `N`, `D`, `w` and `U` (`TaskN`).
  The calling convention is the same: sizes, the bound, the addresses of the arrays, the address of
  the output, and the free pointer last.  The three tasks: the wanted entries of a thin matrix
  product (`thinTask`; Theorem 5 and Corollary 26), #Lop-AE-SparseTri (`lopCountTask`;
  Definition 14) and Lop-AE-SparseTri (`lopDetectTask`; Definition 13).  All three have the same
  instances (`ThinInst`).
* What "solved in time `T`" means for them: `ThinSolvedIn`, `LopSolvedIn`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light

open ThreeSumApsp.Spec

/-! ## The problems for Section 3.4 -/





























/-- An instance stays where it is if no cell below the free pointer changes. -/
theorem TriInst.Pre.keep {x : TriInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr)
    (hs : Kept μ μ' fr := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_92425_0 apspMacro_92425_1);
                                 (first
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_92425_2));
                                                 ((try
                                                       have :=
                                                         apspMacro_92425_2 apspMacro_92425_0 (by omega)));
                                                 (revert apspMacro_92425_2)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((simp [] at apspMacro_92425_1);
                                       (((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_92425_3));
                                                 ((try
                                                       have :=
                                                         apspMacro_92425_3 apspMacro_92425_0 (by omega)));
                                                 (revert apspMacro_92425_3)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_92425_4));
                                                 ((try
                                                       have :=
                                                         apspMacro_92425_4 apspMacro_92425_0 (by omega)));
                                                 (revert apspMacro_92425_4)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (fail
                                           "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                     SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                     its condition K x does not follow from the hypotheses."))))) : x.Pre μ' fr := by
  (obtain ⟨⟩ := id h)
  exact { h with segAB := h.segAB.keep, segBC := h.segBC.keep, segAC := h.segAC.keep }

/-- The free pointer may grow. -/
theorem TriInst.Pre.mono {x : TriInst} {μ : ℕ → ℤ} {fr fr' : ℕ} (h : x.Pre μ fr) (hfr : fr ≤ fr') :
    x.Pre μ fr' :=
  { h with
    belowAB := h.belowAB.trans hfr
    belowBC := h.belowBC.trans hfr
    belowAC := h.belowAC.trans hfr }























































































































































/-! ## The thin matrix product and the lopsided triangle problems -/




























































/-! The ten arguments of a procedure for one of these tasks, as local variables. -/

namespace ThinArg






















end ThinArg

























































end Light

end
end

section


/-!
# Theorem 17, first step: hashing modulo a prime

The first step of the proof of Theorem 17 reduces the weights modulo a prime `p` in the range
`[√D/2, √D)` with few false positives.

* **Counting.**  The number of triples with `S(a,b,c) ≡ 0 (mod p)` is `F(p) + Z₀`
  (`TriangleInstance.countZeroMod_eq`), and it can be read off the product of two matrices over
  `ℤ[x]/(x^p − 1)` (`TriangleInstance.coeff_matP_mul_matQ`,
  `TriangleInstance.F_add_Z₀_eq_sum_coeff`).  There are fewer than `√D` primes in the range
  (`card_primesInRange_lt`).
* **Selecting.**  The prime with the smallest count exists
  (`TriangleInstance.exists_isSelectedPrime`) and has the fewest false positives
  (`TriangleInstance.IsSelectedPrime.F_le`).
* **The bound on `F(p)`**, `TriangleInstance.F_le_of_le_card_primesInRange` and
  `TriangleInstance.exists_F_le`.  A triple is a false positive of at most `log_{√D/2}(3n^ν)` primes
  in the range (`TriangleInstance.card_falsePositive_primes_le`), so the numbers `F(q)` add up to at
  most `n³` times that (`TriangleInstance.sum_F_le`); there are `Ω(√D/log D)` primes in the range
  (`exists_le_card_primesInRange`); `F(p)` is at most the average
  (`TriangleInstance.IsSelectedPrime.F_mul_card_le_sum`); and `log D ≤ 4 log(√D/2)`
  (`log_le_four_mul_log_sqrt_div_two`).  The constant of the bound has a name,
  `Hashing.falsePositiveConst`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ### The primes in the range -/












/-! ### The ring `ℤ[x]/(x^p − 1)` -/






namespace CyclicRing

open Polynomial

variable {p : ℕ}











/-- The coefficient, in terms of the representing polynomial. -/
theorem coeff_apply (hp : p ≠ 0) (r : ℕ) (z : CyclicRing p) :
    coeff hp r z = (AdjoinRoot.modByMonicHom (monic_X_pow_sub_C (1 : ℤ) hp) z).coeff r :=
  rfl

/-- In `ℤ[x]/(x^p − 1)` we have `x^p = 1`. -/
private theorem x_pow_self (p : ℕ) : x p ^ p = 1 := by
  have h : AdjoinRoot.mk ((X : ℤ[X]) ^ p - C 1) ((X : ℤ[X]) ^ p - C 1) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, C_1, map_one] at h
  exact sub_eq_zero.1 h

/-- The coefficient of `x^r` in the power `x^k` of `ℤ[x]/(x^p − 1)` is 1 if `r = k mod p` and 0
otherwise. -/
theorem coeff_x_pow (hp : p ≠ 0) (k r : ℕ) :
    coeff hp r (x p ^ k) = if r = k % p then 1 else 0 := by
  have hred : x p ^ k = x p ^ (k % p) := by
    conv_lhs => rw [← Nat.div_add_mod k p, pow_add, pow_mul, x_pow_self, one_pow, one_mul]
  have hdeg : ((X : ℤ[X]) ^ (k % p)).degree < ((X : ℤ[X]) ^ p - C 1).degree := by
    rw [degree_X_pow, degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
    exact_mod_cast Nat.mod_lt k (Nat.pos_of_ne_zero hp)
  rw [coeff_apply, hred, x, ← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (monic_X_pow_sub_C (1 : ℤ) hp)).2 hdeg, coeff_X_pow]

end CyclicRing

/-- A number `r < p` is the sum of the residues of `u` and `v` in `{0, …, p − 1}`, reduced modulo
`p`, exactly if `u + v ≡ r`. -/
private theorem eq_add_toNat_emod_iff {p r : ℕ} (hp : p ≠ 0) (hr : r < p) (u v : ℤ) :
    r = ((u % (p : ℤ)).toNat + (v % (p : ℤ)).toNat) % p ↔ u + v ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [← Int.natCast_inj, Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg r) (by exact_mod_cast hr),
    eq_comm]
  push_cast
  rw [Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp),
    Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp),
    ← Int.add_emod]

/-! ### Counting the triples with `S(a,b,c) ≡ 0 (mod p)` -/

namespace TriangleInstance

variable {n : ℕ} (T : TriangleInstance ℤ n)



































/-- Proof of Theorem 17: "the coefficient of x^r in (PQ)[a,b] is the number of c ∈ C with w(a,c) +
w(b,c) ≡ r (mod p)". -/
theorem coeff_matP_mul_matQ {p : ℕ} (hp : p ≠ 0) (a b : Fin n) (r : ℕ) (hr : r < p) :
    CyclicRing.coeff hp r ((T.matP p * T.matQ p) a b) =
      ((Finset.univ.filter fun c : Fin n =>
        T.wAC a c + T.wBC b c ≡ (r : ℤ) [ZMOD (p : ℤ)]).card : ℤ) := by
  classical
  -- `(PQ)[a,b]` is the sum over `c` of `x^(w(a,c) mod p + w(b,c) mod p)`, and the coefficient of
  -- `x^r` in each term is 1 or 0.
  rw [Matrix.mul_apply]
  simp only [matP, matQ, Matrix.of_apply, ← pow_add]
  rw [map_sum]
  simp only [CyclicRing.coeff_x_pow]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [eq_add_toNat_emod_iff hp hr]

/-- Proof of Theorem 17: "then F(p) + Z₀ is the sum over the pairs (a,b) ∈ A × B of the coefficient
of x^{−w(a,b) mod p} in (PQ)[a,b]". -/
theorem F_add_Z0_eq_sum_coeff {p : ℕ} (hp : p ≠ 0) :
    ((T.F p + T.Z₀ : ℕ) : ℤ) =
      ∑ a : Fin n, ∑ b : Fin n,
        CyclicRing.coeff hp ((-T.wAB a b) % (p : ℤ)).toNat ((T.matP p * T.matQ p) a b) := by
  classical
  rw [← countZeroMod_eq]
  unfold countZeroMod
  rw [Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hcast := Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp) (-T.wAB a b)
  rw [T.coeff_matP_mul_matQ hp a b _ (Int.toNat_emod_lt (Nat.pos_of_ne_zero hp) _),
    Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  -- `S(a,b,c) ≡ 0` says the same as `w(a,c) + w(b,c) ≡ -w(a,b)`, and `-w(a,b)` is congruent to its
  -- residue.
  have hres : (-T.wAB a b) % (p : ℤ) ≡ -T.wAB a b [ZMOD (p : ℤ)] := Int.mod_modEq _ _
  have hiff : T.S a b c ≡ 0 [ZMOD (p : ℤ)] ↔
      T.wAC a c + T.wBC b c ≡ ((((-T.wAB a b) % (p : ℤ)).toNat : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
    rw [hcast, show T.wAC a c + T.wBC b c ≡ (-T.wAB a b) % (p : ℤ) [ZMOD (p : ℤ)] ↔
        T.wAC a c + T.wBC b c ≡ -T.wAB a b [ZMOD (p : ℤ)] from
      ⟨fun h => h.trans hres, fun h => h.trans hres.symm⟩,
      Int.modEq_iff_dvd, Int.modEq_iff_dvd,
      show 0 - T.S a b c = -T.wAB a b - (T.wAC a c + T.wBC b c) by
        simp only [S]; ring]
  simp only [hiff]

end TriangleInstance


















/-! ### Selecting the prime -/

namespace TriangleInstance

variable {n D p : ℕ} {κ : ℝ} (T : TriangleInstance ℤ n)

/-- Proof of Theorem 17.  There is a prime to select. -/
theorem exists_isSelectedPrime (D : ℕ) (hD : 16 ≤ D) : ∃ p, T.IsSelectedPrime D p := by
  obtain ⟨q, hq⟩ :=
    Nat.exists_prime_half_le_and_lt (Real.sqrt D) (Real.four_le_sqrt_natCast_of_sixteen_le hD)
  exact Finset.exists_min_image (primesInRange D) T.countZeroMod ⟨q, mem_primesInRange.2 hq⟩










/-! ### The bound on the number of false positives of the selected prime -/
















































































end TriangleInstance













































































































end ThreeSumApsp

end
end

section


/-!
# The ring `ℤ[x]/(x^p − 1)` as vectors of `p` integers

The proof of Theorem 17 computes with matrices over the ring `ℤ[x]/(x^p − 1)`.  For a program an
element of the ring is the list of its `p` coefficients (`cycVec`).  This file shows that the
operations of the ring are operations on lists that use no division:

* zero, sums and differences are entrywise (`cycVec_zero`, `cycVec_add`, `cycVec_sub`);
* a power of `x` is a unit vector (`cycVec_x_pow`);
* multiplication is cyclic convolution, "O(p²) word operations" (`cycVec_mul`).  For the proof both
  factors are expanded in powers of `x` (`eq_sum_coeff`), and `x^i x^j` contributes to the
  coefficient of `x^r` exactly if `i + j ≡ r (mod p)`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec




















variable {p : ℕ} (hp : p ≠ 0)

/-! ## Coefficients -/

/-- The representative of degree less than `p` has no coefficients from `p` on. -/
theorem coeff_eq_zero_of_le (z : CyclicRing p) {r : ℕ} (hr : p ≤ r) :
    CyclicRing.coeff hp r z = 0 := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [CyclicRing.coeff_apply, AdjoinRoot.modByMonicHom_mk]
  refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
    (Polynomial.degree_modByMonic_lt f (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp)) ?_)
  rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
  exact_mod_cast hr

/-- An element of the ring is the combination of the powers of `x` with its coefficients. -/
theorem eq_sum_coeff (z : CyclicRing p) :
    z = ∑ i ∈ Finset.range p, CyclicRing.coeff hp i z • CyclicRing.x p ^ i := by
  have hmk := AdjoinRoot.mk_leftInverse (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp) z
  set f := AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp) z with hf
  have hdeg : f.natDegree < p := by
    by_contra hc
    have hlead : f.coeff f.natDegree = 0 := coeff_eq_zero_of_le hp z (not_lt.mp hc)
    rw [Polynomial.leadingCoeff_eq_zero.mp hlead, Polynomial.natDegree_zero] at hc
    exact hc (Nat.pos_of_ne_zero hp)
  conv_lhs => rw [← hmk, Polynomial.as_sum_range' f p hdeg, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    zsmul_eq_mul]
  simp [CyclicRing.coeff_apply, CyclicRing.x, hf]

/-- For `i, j, r < p`: `i + j ≡ r (mod p)` exactly if `j` is `r - i` or `r + p - i`. -/
private theorem eq_add_mod_iff {p i j r : ℕ} (hi : i < p) (hj : j < p) (hr : r < p) :
    r = (i + j) % p ↔ j = if i ≤ r then r - i else r + p - i := by
  by_cases h : i + j < p
  · rw [Nat.mod_eq_of_lt h]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega

/-! ## Vectors -/

/-- A vector has `p` entries. -/
theorem length_cycVec (z : CyclicRing p) : (cycVec hp z).length = p := by
  simp [cycVec]

/-- Entry `r` of the vector is the coefficient of `x^r`. -/
theorem getD_cycVec (z : CyclicRing p) {r : ℕ} (hr : r < p) :
    (cycVec hp z).getD r 0 = CyclicRing.coeff hp r z :=
  List.getD_map_range _ hr 0

/-- The vector of 0. -/
theorem cycVec_zero : cycVec hp 0 = List.replicate p 0 := by
  rw [cycVec, List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hb
  exact map_zero (CyclicRing.coeff hp r)

/-- The vector of a sum. -/
theorem cycVec_add (z w : CyclicRing p) :
    cycVec hp (z + w) = vadd (cycVec hp z) (cycVec hp w) := by
  refine List.ext_getElem (by simp [vadd, length_cycVec]) fun r _ _ => ?_
  simp only [vadd, cycVec, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  exact map_add (CyclicRing.coeff hp r) z w

/-- The vector of a difference. -/
theorem cycVec_sub (z w : CyclicRing p) :
    cycVec hp (z - w) = vsub (cycVec hp z) (cycVec hp w) := by
  refine List.ext_getElem (by simp [vsub, length_cycVec]) fun r _ _ => ?_
  simp only [vsub, cycVec, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  exact map_sub (CyclicRing.coeff hp r) z w

/-- The vector of a power of `x`. -/
theorem cycVec_x_pow (k : ℕ) : cycVec hp (CyclicRing.x p ^ k) = vunit p (k % p) :=
  List.map_congr_left fun r _ => CyclicRing.coeff_x_pow hp k r

/-- Multiplication in the ring is cyclic convolution. -/
theorem cycVec_mul (z w : CyclicRing p) :
    cycVec hp (z * w) = cconv p (cycVec hp z) (cycVec hp w) := by
  refine List.map_congr_left fun r hr => ?_
  have hr' := List.mem_range.mp hr
  -- Expand both factors in powers of x.
  conv_lhs => rw [eq_sum_coeff hp z, eq_sum_coeff hp w, Finset.sum_mul_sum]
  rw [map_sum, List.sum_map_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  -- For each i, only one j contributes to the coefficient of x^r.
  have hj : (if i ≤ r then r - i else r + p - i) < p := by split_ifs <;> omega
  rw [getD_cycVec hp z hi', getD_cycVec hp w hj, map_sum]
  simp only [smul_mul_smul_comm, ← pow_add, map_zsmul, CyclicRing.coeff_x_pow, smul_eq_mul]
  rw [Finset.sum_eq_single (if i ≤ r then r - i else r + p - i)]
  · rw [if_pos ((eq_add_mod_iff hi' hj hr').mpr rfl), mul_one]
  · intro j hj' hne
    rw [if_neg fun h => hne ((eq_add_mod_iff hi' (Finset.mem_range.mp hj') hr').mp h), mul_zero]
  · exact fun h => absurd (Finset.mem_range.mpr hj) h

end ThreeSumApsp.Spec

end
end

section


/-!
# Hashing modulo a prime (proof of Theorem 17), on numbers and lists

The reduction of Theorem 17 hashes the weights modulo a prime `p` of the window `√D/2 ≤ p < √D` and
selects the prime with the fewest triples `(a,b,c)` with `S(a,b,c) ≡ 0 (mod p)`, where
`S(a,b,c) = w(a,b) + w(b,c) + w(a,c)`.  This file has the parts of this step that a program
computes:

* the residue of a weight as a natural number below `p` (`resid`, `residList`);
* the entries of the matrices `P` and `Q` of the proof of Theorem 17 as unit vectors (`cycVec_matP`,
  `cycVec_matQ`), and the count of the triples, read off the vectors of `PQ` (`countZeroMod_eq`);
* the primes of the window by comparisons of integers (`primesList`, `primesInRange_eq`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Residues -/




/-- The residue, as an integer. -/
theorem resid_cast {p : ℕ} (hp : p ≠ 0) (w : ℤ) : (resid p w : ℤ) = w % (p : ℤ) :=
  Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp) w

/-- The residue is less than `p`. -/
theorem resid_lt {p : ℕ} (hp : p ≠ 0) (w : ℤ) : resid p w < p :=
  Int.toNat_emod_lt (Nat.pos_of_ne_zero hp) w

/-- The residue is the number below `p` that is congruent to `w`. -/
theorem resid_eq_iff {p : ℕ} (hp : p ≠ 0) (w : ℤ) {r : ℕ} (hr : r < p) :
    resid p w = r ↔ w ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg r) (Int.ofNat_lt.2 hr), ← resid_cast hp,
    Nat.cast_inj]

/-- The residue of `-w` from the residue of `w`. -/
theorem resid_neg {p : ℕ} (hp : p ≠ 0) (w : ℤ) : resid p (-w) = (p - resid p w) % p := by
  refine (resid_eq_iff hp _ (Nat.mod_lt _ (Nat.pos_of_ne_zero hp))).2 ?_
  have hself : (p : ℤ) ≡ 0 [ZMOD (p : ℤ)] := Int.emod_self.trans (Int.zero_emod _).symm
  have hsub := (Int.mod_modEq ((p : ℤ) - w % p) p).trans (hself.sub (Int.mod_modEq w p))
  rw [Int.natCast_mod, Nat.cast_sub (resid_lt hp w).le, resid_cast hp]
  rw [zero_sub] at hsub
  exact hsub.symm




/-- The residues of a list, read with a default: beyond the end of the list both sides are 0. -/
theorem getD_residList (p : ℕ) (l : List ℤ) (i : ℕ) :
    (residList p l).getD i 0 = resid p (l.getD i 0) := by
  rw [residList, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [resid]







/-! ## The count of the proof of Theorem 17 -/

/-- Proof of Theorem 17: the entry `P[a,c] = x^{w(a,c) mod p}` is a unit vector. -/
theorem cycVec_matP {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ} (hp : p ≠ 0) (a c : Fin n) :
    cycVec hp (T.matP p a c) = vunit p (resid p (T.wAC a c)) := by
  rw [TriangleInstance.matP, Matrix.of_apply, cycVec_x_pow]
  exact congrArg (vunit p) (Nat.mod_eq_of_lt (resid_lt hp _))

/-- Proof of Theorem 17: the entry `Q[c,b] = x^{w(b,c) mod p}` is a unit vector. -/
theorem cycVec_matQ {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ} (hp : p ≠ 0) (c b : Fin n) :
    cycVec hp (T.matQ p c b) = vunit p (resid p (T.wBC b c)) := by
  rw [TriangleInstance.matQ, Matrix.of_apply, cycVec_x_pow]
  exact congrArg (vunit p) (Nat.mod_eq_of_lt (resid_lt hp _))

/-- Proof of Theorem 17: the count of the triples with `S(a,b,c) ≡ 0 (mod p)` is "the sum over the
pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]". -/
theorem countZeroMod_eq {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ} (hp : p ≠ 0) :
    (T.countZeroMod p : ℤ) =
      ∑ a, ∑ b, (cycVec hp ((T.matP p * T.matQ p) a b)).getD (resid p (-T.wAB a b)) 0 := by
  rw [TriangleInstance.countZeroMod_eq, TriangleInstance.F_add_Z0_eq_sum_coeff T hp]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    (getD_cycVec hp _ (resid_lt hp _)).symm

/-! ## The primes of the window -/





/-- The comparisons with `√D` are comparisons of integers. -/
theorem primesInRange_eq (D : ℕ) : primesInRange D = (primesList D).toFinset := by
  ext q
  have hlow : Real.sqrt D / 2 ≤ (q : ℝ) ↔ D ≤ 4 * q ^ 2 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), Real.sqrt_le_left (by positivity),
      show ((q : ℝ) * 2) ^ 2 = ((4 * q ^ 2 : ℕ) : ℝ) by push_cast; ring, Nat.cast_le]
  have hhigh : (q : ℝ) < Real.sqrt D ↔ q ^ 2 < D := by
    rw [Real.lt_sqrt (by positivity)]
    exact_mod_cast Iff.rfl
  simp [primesInRange, primesList, hlow, hhigh]

/-- The primes of the window, without the bound `q < D` of the search. -/
theorem mem_primesList {D q : ℕ} : q ∈ primesList D ↔ q.Prime ∧ D ≤ 4 * q ^ 2 ∧ q ^ 2 < D := by
  simp only [primesList, List.mem_filter, List.mem_range, decide_eq_true_eq, and_iff_right_iff_imp]
  exact fun h => (Nat.le_self_pow (by norm_num) q).trans_lt h.2.2

/-- A prime of the window is at most `⌊√D⌋`. -/
theorem le_sqrt_of_mem_primesList {D q : ℕ} (h : q ∈ primesList D) : q ≤ Nat.sqrt D :=
  Nat.le_sqrt'.2 (mem_primesList.1 h).2.2.le

/-- The window has at most `⌊√D⌋` primes. -/
theorem length_primesList_le (D : ℕ) : (primesList D).length ≤ Nat.sqrt D := by
  have hnodup : (primesList D).Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  calc (primesList D).toFinset.card ≤ (Finset.Icc 1 (Nat.sqrt D)).card := by
        refine Finset.card_le_card fun q hq => ?_
        rw [List.mem_toFinset] at hq
        exact Finset.mem_Icc.2 ⟨(mem_primesList.1 hq).1.one_le, le_sqrt_of_mem_primesList hq⟩
    _ = Nat.sqrt D := by simp

end ThreeSumApsp.Spec

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



















/-- A sum over the indices below `m * n`, row by row: the index `a * n + b` has row `a` and column
`b`. -/
theorem sum_range_mul {M : Type*} [AddCommMonoid M] (m n : ℕ) (F : ℕ → M) :
    ∑ i ∈ range (m * n), F i = ∑ a ∈ range m, ∑ b ∈ range n, F (a * n + b) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

end Finset













end
end

section


/-!
# Strassen's algorithm on lists, and the count of the proof of Theorem 17

Proof of Theorem 17: "Computing PQ takes […] O(n^{log₂ 7}) with Strassen's algorithm".
`strassenList` multiplies two `2^K × 2^K` matrices over `ℤ[x]/(x^p - 1)`, given as lists in Z-order,
and `countOf` reads the number of triples `(a,b,c)` with `S(a,b,c) = w(a,b) + w(b,c) + w(a,c) ≡ 0
(mod p)` off the product.

1. `zRing hp K α` is the list of the matrix `α` over the ring.  The operations on lists are the
   operations of the ring, entry by entry (`zRing_add`, `zRing_sub`), and the quadrants of a matrix
   are the quarters of its list (`quarter_zRing`, `zRing_succ`).
2. `strassenList_zRing`: the algorithm computes the product.  By induction on `K`; Strassen's seven
   products give the four quadrants of the product by an identity that holds summand by summand.
   It makes `7^K` multiplications in the ring, which is `O(n^{log₂ 7})` (`seven_pow_clog_le`).
3. The lists that the routine fills are the matrices `P` and `Q` of the proof of Theorem 17, padded
   with zeros to `2^K` rows and columns (`matPList_eq_zRing`, `matQList_eq_zRing`), and the padding
   does not change the entries of the product (`sum_padP_mul_padQ`).
4. `countOf_eq`: the count is the count of the proof of Theorem 17.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

open Finset

/-! ## Matrices over the ring, as lists -/

section Ring

variable {p : ℕ} (hp : p ≠ 0) (K : ℕ)





/-- The list of a sum of matrices. -/
theorem zRing_add (α β : ℕ → ℕ → CyclicRing p) :
    vadd (zRing hp K α) (zRing hp K β) = zRing hp K fun a c => α a c + β a c := by
  unfold zRing zList vadd
  rw [List.zipWith_flatMap_range _ _ _ _ (fun _ => length_cycVec hp _) fun _ => length_cycVec hp _]
  exact List.flatMap_congr fun z _ => (cycVec_add hp _ _).symm

/-- The list of a difference of matrices. -/
theorem zRing_sub (α β : ℕ → ℕ → CyclicRing p) :
    vsub (zRing hp K α) (zRing hp K β) = zRing hp K fun a c => α a c - β a c := by
  unfold zRing zList vsub
  rw [List.zipWith_flatMap_range _ _ _ _ (fun _ => length_cycVec hp _) fun _ => length_cycVec hp _]
  exact List.flatMap_congr fun z _ => (cycVec_sub hp _ _).symm

/-- The quadrants of a matrix are the quarters of its list. -/
theorem quarter_zRing (α : ℕ → ℕ → CyclicRing p) {t : ℕ} (ht : t < 4) :
    quarter (4 ^ K * p) t (zRing hp (K + 1) α) =
      zRing hp K fun a c => α (a + t / 2 * 2 ^ K) (c + t % 2 * 2 ^ K) :=
  quarter_zList _ (fun _ _ => length_cycVec hp _) ht

/-- A matrix is put together from its four quadrants. -/
theorem zRing_succ (α : ℕ → ℕ → CyclicRing p) :
    zRing hp (K + 1) α =
      zRing hp K (fun a c => α a c) ++ zRing hp K (fun a c => α a (c + 2 ^ K)) ++
      zRing hp K (fun a c => α (a + 2 ^ K) c) ++ zRing hp K fun a c => α (a + 2 ^ K) (c + 2 ^ K) :=
  zList_succ _ fun _ _ => length_cycVec hp _

end Ring

/-! ## Strassen's algorithm -/



















/-- A sum over twice as many indices. -/
private theorem sum_range_two_pow_succ {R : Type} [AddCommMonoid R] (K : ℕ) (f : ℕ → R) :
    ∑ c ∈ range (2 ^ (K + 1)), f c =
      ∑ c ∈ range (2 ^ K), f c + ∑ c ∈ range (2 ^ K), f (c + 2 ^ K) := by
  rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
  simp only [Nat.add_comm]

/-- **Strassen's algorithm computes the product**, for matrices over the ring. -/
theorem strassenList_zRing {p : ℕ} (hp : p ≠ 0) (K : ℕ) (α β : ℕ → ℕ → CyclicRing p) :
    strassenList p K (zRing hp K α) (zRing hp K β) =
      zRing hp K fun a b => ∑ c ∈ range (2 ^ K), α a c * β c b := by
  induction K generalizing α β with
  | zero => simp [strassenList, zRing, zList, zRow_zero, zCol_zero, cycVec_mul]
  | succ K ih =>
    -- The quarters of the two lists are the quadrants, and the seven products are products.
    have hq0 := fun γ => quarter_zRing hp K γ (show 0 < 4 by norm_num)
    have hq1 := fun γ => quarter_zRing hp K γ (show 1 < 4 by norm_num)
    have hq2 := fun γ => quarter_zRing hp K γ (show 2 < 4 by norm_num)
    have hq3 := fun γ => quarter_zRing hp K γ (show 3 < 4 by norm_num)
    simp only [Nat.reduceDiv, Nat.reduceMod, Nat.zero_mul, Nat.one_mul, Nat.add_zero]
      at hq0 hq1 hq2 hq3
    simp only [strassenList, hq0, hq1, hq2, hq3, zRing_add, zRing_sub, ih]
    -- Strassen's identities, one for each quadrant of the product, summand by summand.
    rw [zRing_succ]
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_ <;>
      refine congrArg (zRing hp K) (funext₂ fun a b => ?_) <;>
      rw [sum_range_two_pow_succ] <;>
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib] <;>
      exact Finset.sum_congr rfl fun c _ => by ring







/-! ## The count of the proof of Theorem 17 -/


























section Count

variable {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ}









/-- The padding does not change the entries of the product. -/
theorem sum_padP_mul_padQ (p : ℕ) {N : ℕ} (hN : n ≤ N) (a b : Fin n) :
    ∑ c ∈ range N, padP T p a c * padQ T p c b = (T.matP p * T.matQ p) a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hpad : ∑ x ∈ range k, padP T p a (n + x) * padQ T p (n + x) b = 0 :=
    Finset.sum_eq_zero fun x _ => by simp [padP]
  rw [Finset.sum_range_add, hpad, add_zero, Matrix.mul_apply, Finset.sum_range]
  exact Finset.sum_congr rfl fun c _ => by simp [padP, padQ]

variable (n) (AB BC AC : List ℤ)

/-- The first list that the routine fills is the matrix `P`, padded. -/
theorem matPList_eq_zRing (hp : p ≠ 0) (K : ℕ) :
    matPList n p K (residList p AC) = zRing hp K (padP (triOf n AB BC AC) p) := by
  refine congrArg (zList K) (funext₂ fun a c => ?_)
  rw [padP]
  split_ifs with h
  · rw [cycVec_matP, getD_residList]
    rfl
  · exact (cycVec_zero hp).symm

/-- The second list that the routine fills is the matrix `Q`, padded. -/
theorem matQList_eq_zRing (hp : p ≠ 0) (K : ℕ) :
    matQList n p K (residList p BC) = zRing hp K (padQ (triOf n AB BC AC) p) := by
  refine congrArg (zList K) (funext₂ fun c b => ?_)
  rw [padQ]
  split_ifs with h
  · rw [cycVec_matQ, getD_residList]
    rfl
  · exact (cycVec_zero hp).symm

/-- **The count of the proof of Theorem 17**: `countOf`, computed with Strassen's algorithm from the
three lists of weights, is the number of triples `(a,b,c)` with `S(a,b,c) ≡ 0 (mod p)`. -/
theorem countOf_eq (hp : p ≠ 0) :
    countOf n p AB BC AC = (triOf n AB BC AC).countZeroMod p := by
  have hnK : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  -- The two lists are `P` and `Q`, padded (step 3), and Strassen's algorithm gives their product
  -- (step 2); both sides become sums over the pairs `(a, b)`.
  rw [countZeroMod_eq _ hp, countOf, matPList_eq_zRing n AB BC AC hp,
    matQList_eq_zRing n AB BC AC hp, strassenList_zRing, countBy, List.sum_map_range, sum_range_mul,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  -- The place `a n + b` has row `a` and column `b`; `(p - r) % p` is the residue of `-w(a,b)`; the
  -- number read from the list is that coefficient of `(PQ)[a,b]`.
  rw [Nat.mul_add_div_of_lt b.isLt, Nat.mul_add_mod_of_lt b.isLt, getD_residList, ← resid_neg hp,
    zRing,
    getD_zList _ (fun _ _ => length_cycVec hp _) (a.isLt.trans_le hnK) (b.isLt.trans_le hnK)
      (resid_lt hp _),
    sum_padP_mul_padQ _ p hnK a b]
  rfl

end Count

end ThreeSumApsp.Spec

end
end

section


/-!
# The count of the proof of Theorem 17, read off the product PQ

"then F(p) + Z₀ is the sum over the pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in
(PQ)[a,b]."  Here F(p) is the number of false positives of p, that is, of triples with S(a,b,c) =
w(a,b) + w(b,c) + w(a,c) ≠ 0 and p ∣ S(a,b,c), and Z₀ is the number of zero triangles.

This file proves that the routine countZero returns this sum, `countBy`.  It does not prove that the
sum is F(p) + Z₀: that is `countOf_eq`, a theorem about lists with no program in it.

countZero(rm, rab, mort, n, p): the cells from rm hold the product PQ, a matrix of 4^K vectors of p
coefficients each, in Z-order, where 2^K ≥ n; the cells from rab hold the residues of the weights
w(a,b) mod p, that of (a, b) at place a n + b; the cells from mort hold the table of `spread`, from
which the place of a pair in Z-order is formed.  The routine goes through the pairs (a, b) in the
order of their places a n + b, reads the residue ϱ of w(a,b), forms (p - ϱ) mod p by one test, and
adds the coefficient number (p - ϱ) mod p of the vector of (a, b) (`countTerm`,
`countZeroAdd_spec`); then it steps to the next pair.  The loop is `countZero_spec`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace CountZero
















end CountZero






































namespace CountZeroPre

variable {μ : ℕ → ℤ} {rm rab mort n K p : ℕ} {RM : List ℤ} {RAB : List ℕ} {V : ℤ} {t : ℕ}

/-- The place of the term of the pair number t lies in the list RM of the 4^K p coefficients. -/
theorem index_lt (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) (ht : t < n * n) :
    zIdx (t / n) (t % n) * p + (p - RAB.getD t 0) % p < 4 ^ K * p := by
  have hn := pre.n_le
  have hp := pre.res.getD_lt ht
  have hrow : t / n < n := Nat.div_lt_of_lt_mul' ht
  have hcol : t % n < n := Nat.mod_lt_of_lt_mul ht
  exact Nat.mul_add_lt_mul (zIdx_lt (by omega) (by omega)) (Nat.mod_lt _ (by omega))

/-- The term of the pair number t. -/
theorem readTerm (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) (ht : t < n * n) :
    μ (rm + (zIdx (t / n) (t % n) * p + (p - RAB.getD t 0) % p)) = countTerm n p RM RAB t :=
  pre.mat.read (pre.index_lt ht)

theorem abs_countTerm_le (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) (ht : t < n * n) :
    |countTerm n p RM RAB t| ≤ V := by
  rw [← pre.readTerm ht]
  exact pre.mat.abs_read_le (pre.index_lt ht)

end CountZeroPre

variable {μ : ℕ → ℤ} {rm rab mort n K p : ℕ} {RM : List ℤ} {RAB : List ℕ} {V : ℤ}

open CountZero in
/-- **The term of the pair number t is added.** -/
theorem countZeroAdd_spec (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) {t : ℕ}
    (ht : t < n * n) (S ex : ℤ) (hfits : |S + countTerm n p RM RAB t| ≤ lim.word) :
    Ends lim P d countZeroAdd
      ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, (t / n : ℕ), (t % n : ℕ), S, ex], μ⟩ 34
      fun σ' => ∃ ex' : ℤ, σ' = ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, (t / n : ℕ),
        (t % n : ℕ), S + countTerm n p RM RAB t, ex'], μ⟩ := by
  ((obtain ⟨⟩ := id pre); (obtain ⟨⟩ := id pre.mat); (obtain ⟨⟩ := id pre.res);
    (obtain ⟨⟩ := id pre.table))
  have hrow : t / n < n := Nat.div_lt_of_lt_mul' ht
  have hcol : t % n < n := Nat.mod_lt_of_lt_mul ht
  have hreadA : μ (mort + t / n) = (spread (t / n) : ℕ) :=
    seg_spreadList_get pre.table.seg (by omega)
  have hreadB : μ (mort + t % n) = (spread (t % n) : ℕ) :=
    seg_spreadList_get pre.table.seg (by omega)
  have hreadR := pre.res.read ht
  have hrho := pre.res.getD_lt ht
  have hidx := pre.index_lt ht
  have hterm := pre.readTerm ht
  have hp : p ≤ 4 ^ K * p := Nat.le_mul_of_pos_left p (by positivity)
  replace hfits := abs_le.1 hfits
  generalize countTerm n p RM RAB t = term at *
  generalize RAB.getD t 0 = rho at *
  unfold zIdx at hidx hterm
  generalize t / n = a at *
  generalize t % n = b at *
  generalize spread a = sa at *
  generalize spread b = sb at *
  -- ex := rab[t]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (rho : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hreadR]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hreadR] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadR] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- if ex ≠ 0 then ex := p - ex
  have label : Ends lim P d (.ite ((Light.Cond.eq (v Expo) (k 0))) .skip (.set Expo (((Light.Expr.op Light.Op.sub) (v Prime) (v Expo)))))
      ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, a, b, S, (rho : ℕ)], μ⟩ 8 fun σ' =>
        σ' = ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, a, b, S, ((p - rho) % p : ℕ)], μ⟩ := by
    refine Ends.iteLast (fun h0 => Ends.skip ?_) fun h0 => Ends.setTo (p - rho : ℕ) ?_
    · obtain rfl : rho = 0 := by simpa using h0
      rw [Nat.sub_zero, Nat.mod_self]
    · have h0 : rho ≠ 0 := by simpa using h0
      rw [Nat.mod_eq_of_lt (by omega)]
      rfl
  refine Ends.next 8 (label.mono le_rfl ?_)
  rintro _ rfl
  generalize (p - rho) % p = s at hidx hterm
  -- sum := sum + rm[(2 mort[a] + mort[b]) p + ex]
  have hidxZ : (2 * (sa : ℤ) + sb) * p + s < (4 ^ K * p : ℕ) := by exact_mod_cast hidx
  have hle : 2 * (sa : ℤ) + sb ≤ (2 * (sa : ℤ) + sb) * p :=
    le_mul_of_one_le_right (by positivity) (by exact_mod_cast (by omega : 1 ≤ p))
  have haddr : ((rm : ℤ) + (2 * (sa : ℤ) + sb) * p + s).toNat = rm + ((2 * sa + sb) * p + s) := by
    rw [show (rm : ℤ) + (2 * (sa : ℤ) + sb) * p + s = ((rm + ((2 * sa + sb) * p + s) : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (S + term) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hreadA,
                hreadB, haddr, hterm]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hreadA, hreadB, haddr, hterm] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadA, hreadB, haddr,
                hterm] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  exact ⟨_, rfl⟩

open CountZero in
/-- **countZero** returns the count and leaves the memory as it was. -/
theorem countZero_spec (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) :
    Ends lim P d countZeroBody ⟨frame [rm, rab, mort, n, p], μ⟩ (countZeroTime n) fun σ' =>
      σ'.loc 0 = countBy n p RM RAB ∧ σ'.mem = μ := by
  ((obtain ⟨⟩ := id pre); (obtain ⟨⟩ := id pre.mat); (obtain ⟨⟩ := id pre.res);
    (obtain ⟨⟩ := id pre.table))
  unfold countZeroTime
  -- nn := n n; a := 0; b := 0; sum := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (n * n : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
          (0 : ℕ)
            -- for t < nn
            
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
  -- for t < nn
  refine Ends.next _ (Ends.for (fun t σ => ∃ ex : ℤ,
      σ = ⟨frame [rm, rab, mort, n, p, (n * n : ℕ), t, (t / n : ℕ), (t % n : ℕ),
        ∑ i ∈ Finset.range t, countTerm n p RM RAB i, ex], μ⟩ ∧
      |∑ i ∈ Finset.range t, countTerm n p RM RAB i| ≤ t * V) (n * n) 48
    ?start ?round ?done ?bound (hT := le_rfl))
  case start =>
    refine ⟨0, ?_, by simp⟩
    rw [update_frame_setLocal, ← frame_append_zeros _ 1, Nat.zero_div, Nat.zero_mod]
    rfl
  case bound =>
    rintro t _ - - ⟨ex, rfl, -⟩
    simp
  case round =>
    rintro t _ ht - ⟨ex, rfl, hsum⟩
    have hV := pre.abs_countTerm_le ht
    -- The new sum fits in a word.
    have hnew : |∑ i ∈ Finset.range (t + 1), countTerm n p RM RAB i| ≤ ((t + 1 : ℕ) : ℤ) * V := by
      rw [Finset.sum_range_succ]
      refine (abs_add_le _ _).trans ?_
      push_cast
      linarith
    have hfits := hnew.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast ht)
      ((abs_nonneg _).trans hV)).trans pre.sum_le)
    rw [Finset.sum_range_succ] at hfits
    refine Ends.next 34 ((countZeroAdd_spec pre ht _ ex hfits).mono le_rfl ?_)
    rintro _ ⟨ex', rfl⟩
    have hn : 0 < n := Nat.pos_of_ne_zero fun e => by simp [e] at ht
    refine Ends.nextPair ?_ hn (by omega) (by omega) rfl rfl rfl
    exact ⟨by simp, ex', by rw [update_frame_setLocal, Finset.sum_range_succ]; rfl, hnew⟩
  case done =>
    rintro _ - ⟨ex, rfl, -⟩
    -- return sum
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
          Light.Ends.setToThen (∑ i ∈ Finset.range (n * n), countTerm n p RM RAB i)
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
    exact ⟨(List.sum_map_range _ _).symm, rfl⟩

/-- **countZero** as a procedure. -/
theorem countZero_meets {μ : ℕ → ℤ} {q rm rab mort n K p : ℕ} {RM : List ℤ} {RAB : List ℕ} {V : ℤ}
    (hP : P[q]? = some countZeroBody) (pre : CountZeroPre lim μ rm rab mort n K p RM RAB V) :
    Meets lim P q d [rm, rab, mort, n, p] μ (countZeroTime n) fun r μ' =>
      r = countBy n p RM RAB ∧ μ' = μ :=
  Meets.of_body hP (countZero_spec pre)

end Light.Sec3

end
end

section


/-!
# The table of the sizes of Strassen's recursion

szTable(dst, p, J) writes the sizes p, 4p, …, 4^J p of the matrices of Strassen's recursion, the
list `szList p J`, and changes nothing else (`szTable_spec`, `szTable_meets`).
-/

@[expose] public section

namespace Light.Sec3

variable {lim : Limits} {P : Program} {d : ℕ}




/-- The table of the sizes has J + 1 entries. -/
@[simp] theorem length_szList (p J : ℕ) : (szList p J).length = J + 1 := by simp [szList]

namespace SzTable








end SzTable















/-- One more entry of the table. -/
theorem szList_succ (p J : ℕ) :
    szList p (J + 1) = szList p J ++ [((4 ^ (J + 1) * p : ℕ) : ℤ)] := by
  simp [szList, List.range_succ]







/-- **szTable** writes p, 4p, …, 4^J p and changes nothing else. -/
theorem szTable_spec {μ : ℕ → ℤ} {dst p J : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (h4 : (4 : ℤ) ≤ lim.word) (hdst : dst + (J + 1) ≤ lim.space)
    (hp : ((4 ^ J * p : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d szTableBody ⟨frame [dst, p, J], μ⟩ (tSzTable J) fun σ' =>
      Seg σ'.mem dst (szList p J) ∧ SameOutside μ σ'.mem dst (J + 1) := by
  have hfits : ∀ j ≤ J, ((4 ^ j * p : ℕ) : ℤ) ≤ lim.word := fun j hj =>
    le_trans (by exact_mod_cast Nat.mul_le_mul_right p (Nat.pow_le_pow_right (by norm_num) hj)) hp
  unfold tSzTable
  -- exp := 0; entry := p; dst[0] := entry
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen p ?_ ?_ ?_);
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
    (refine Light.Ends.storeToThen dst p ?_ ?_ ?_);
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
  -- while exp < J
  refine Ends.whileBlock (SzInv μ dst p J) J ?start ?round ?done
  case start =>
    refine ⟨Function.update μ dst p, by simp, ?_, SameOutside.refl.update ⟨by omega, by omega⟩ _⟩
    simpa [szList] using (Seg.nil (μ := μ) (a := dst)).snoc p
  case round =>
    rintro j _ hj ⟨μ', rfl, seg, rest⟩
    have hnext := hfits (j + 1) hj
    have hfour : 4 ^ (j + 1) * p = 4 * (4 ^ j * p) := by ring
    have haddr : ((dst : ℤ) + ((j : ℤ) + 1)).toNat = dst + (szList p j).length := by
      rw [length_szList]
      omega
    -- entry := 4 entry; exp := exp + 1; dst[exp] := entry
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_, Function.update μ' (dst + (szList p j).length)
      ((4 ^ (j + 1) * p : ℕ) : ℤ), ?_, szList_succ p j ▸ seg.snoc _,
      rest.update ⟨by omega, by rw [length_szList]; omega⟩ _⟩
    · rw [hfour] at hnext
      generalize 4 ^ j * p = q at hnext
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))
    · rw [hfour]
      simp [update_frame_setLocal, haddr]
  case done =>
    rintro _ ⟨μ', rfl, seg, rest⟩
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), seg, rest⟩

/-- **szTable** as a procedure. -/
theorem szTable_meets {μ : ℕ → ℤ} {q dst p J : ℕ} (hP : P[q]? = some szTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (h4 : (4 : ℤ) ≤ lim.word) (hdst : dst + (J + 1) ≤ lim.space)
    (hp : ((4 ^ J * p : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, J] μ (tSzTable J) fun _ μ' =>
      Seg μ' dst (szList p J) ∧ SameOutside μ μ' dst (J + 1) :=
  Meets.of_body hP (szTable_spec hw h4 hdst hp)

end Light.Sec3

end
end

section


/-!
# Vectors: sums, differences, and the product in ℤ[x]/(x^p - 1)

The proof of Theorem 17 computes with matrices over the ring ℤ[x]/(x^p - 1); an element of the ring
is a vector of p integers, and a ring operation takes "O(p²) word operations".

* vlin(dst, a, b, n, s): dst[i] := a[i] + s b[i] for i < n, with s = 1 or s = -1; dst may be the
  segment a itself (accumulation).  It is one pass (`vlin_spec`), and what it writes is `vadd` or
  `vsub` (`vlinList_one`, `vlinList_neg_one`).
* cconv(dst, a, b, p): dst := the cyclic convolution of a and b.  The inner loop adds up the p terms
  of one entry (`cconvEntry_spec`), the outer loop stores the p entries (`cconv_spec`).  The partial
  sums stay below p α β if the entries of a and b are bounded by α and β (`abs_convPartialSum_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Sums and differences -/

namespace Vlin









end Vlin









/-- With s = 1 it is the sum. -/
theorem vlinList_one (A B : List ℤ) : vlinList 1 A B = vadd A B := by
  simp [vlinList, vadd]

/-- With s = -1 it is the difference. -/
theorem vlinList_neg_one (A B : List ℤ) : vlinList (-1) A B = vsub A B := by
  unfold vlinList vsub
  congr 1
  funext x y
  ring















open Vlin in
/-- **vlin** writes a + s b to dst and changes nothing else, in at most 23 n + 6 steps. -/
theorem vlin_spec {μ : ℕ → ℤ} {dst a b n : ℕ} {s V : ℤ} {A B : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (pre : VlinPre lim μ dst a b n s V A B) :
    Ends lim P d vlinBody ⟨frame [dst, a, b, n, s], μ⟩ (23 * n + 6) fun σ' =>
      Seg σ'.mem dst (vlinList s A B) ∧ SameOutside μ σ'.mem dst n := by
  ((obtain ⟨⟩ := id pre); (obtain ⟨⟩ := id pre.opA); (obtain ⟨⟩ := id pre.opB))
  refine Ends.pass (x := Len) (y := Dst) (dst := dst) (n := n) (vlinAt s A B) ?round ?done hw
    pre.space rfl rfl
  case round =>
    intro j hj
    -- The two cells that round j reads have not been written yet.
    have hreadA : wrote μ dst (vlinAt s A B) j (a + j) = A.getD j 0 :=
      (wrote_rest (by omega)).trans (pre.opA.read hj)
    have hreadB : wrote μ dst (vlinAt s A B) j (b + j) = B.getD j 0 :=
      (wrote_rest (by omega)).trans (pre.opB.read hj)
    have hx : |A.getD j 0| ≤ V := pre.opA.read hj ▸ pre.opA.abs_read_le hj
    have hy : |B.getD j 0| ≤ V := pre.opB.read hj ▸ pre.opB.abs_read_le hj
    have hsy : |s * B.getD j 0| ≤ V := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) pre.sign).trans hy
    rw [abs_le] at hx hsy
    rw [vlinAt]
    generalize A.getD j 0 = x at hreadA hx
    generalize B.getD j 0 = y at hreadB hsy
    simp [Limits.Addr, abs_le, hreadA, hreadB, -abs_mul]
    omega
  case done =>
    refine ⟨fun i hi => ?_, sameOutside_wrote (j := n) le_rfl⟩
    have hi' : i < n := by
      simp only [vlinList, List.length_zipWith] at hi
      omega
    change wrote μ dst (vlinAt s A B) n (dst + i) = _
    simp only [vlinList, List.getElem_zipWith]
    rw [wrote_done hi', vlinAt, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)]

/-- **vlin** as a procedure. -/
theorem vlin_meets {μ : ℕ → ℤ} {pVlin dst a b n : ℕ} {s V : ℤ} {A B : List ℤ}
    (hP : P[pVlin]? = some vlinBody) (hw : (lim.space : ℤ) ≤ lim.word)
    (pre : VlinPre lim μ dst a b n s V A B) :
    Meets lim P pVlin d [dst, a, b, n, s] μ (23 * n + 6) fun _ μ' =>
      Seg μ' dst (vlinList s A B) ∧ SameOutside μ μ' dst n :=
  Meets.of_body hP (vlin_spec hw pre)

/-! ## The product -/









/-- One more term. -/
theorem convPartialSum_succ (p : ℕ) (A B : List ℤ) (r j : ℕ) :
    convPartialSum p A B r (j + 1) = convPartialSum p A B r j + convTerm p A B r j :=
  List.sum_range_succ _ _

/-- The convolution is the list of these sums. -/
theorem cconv_eq_map_convPartialSum (p : ℕ) (A B : List ℤ) :
    cconv p A B = (List.range p).map fun r => convPartialSum p A B r p := rfl

section bounds

variable {p : ℕ} {A B : List ℤ} {α β : ℤ}

/-- A term is at most α β in absolute value. -/
theorem abs_convTerm_le (leA : AbsLe A α) (leB : AbsLe B β) (hα : 0 ≤ α) (hβ : 0 ≤ β) (r i : ℕ) :
    |convTerm p A B r i| ≤ α * β := by
  rw [convTerm, abs_mul]
  exact mul_le_mul (AbsLe.abs_getD_le hα leA _) (AbsLe.abs_getD_le hβ leB _) (abs_nonneg _) hα

/-- A sum of j terms is at most j α β in absolute value. -/
theorem abs_convPartialSum_le (leA : AbsLe A α) (leB : AbsLe B β) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (r j : ℕ) :
    |convPartialSum p A B r j| ≤ j * (α * β) := by
  simpa [convPartialSum] using List.abs_sum_map_le (List.range j) (convTerm p A B r)
    fun i _ => abs_convTerm_le leA leB hα hβ r i

end bounds

namespace Cconv












end Cconv




























section cconv

variable {μ : ℕ → ℤ} {dst a b p r : ℕ} {α β : ℤ} {A B : List ℤ}

open Cconv in
/-- **One term of cconv.** -/
theorem cconvTerm_spec (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (hr : r < p) {i : ℕ} (hi : i < p) (t : ℤ) :
    Ends lim P d cconvTerm ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, t], μ⟩ 24 fun σ' =>
      ∃ t', σ' = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r (i + 1), t'], μ⟩ := by
  obtain ⟨opA, opB, hword, hα, hβ, room⟩ := pre
  ((obtain ⟨⟩ := id opA); (obtain ⟨⟩ := id opB))
  have hreadA : μ (a + i) = A.getD i 0 := opA.read hi
  have hterm := abs_le.1 (abs_convTerm_le (p := p) opA.bound opB.bound hα hβ r i)
  have hsum := abs_le.1 (abs_convPartialSum_le (p := p) opA.bound opB.bound hα hβ r (i + 1))
  have hfits : ((i + 1 : ℕ) : ℤ) * (α * β) ≤ lim.word :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) (mul_nonneg hα hβ)).trans hword
  have hone : α * β ≤ ((i + 1 : ℕ) : ℤ) * (α * β) :=
    le_mul_of_one_le_left (mul_nonneg hα hβ) (by push_cast; omega)
  rw [convPartialSum_succ] at hsum ⊢
  -- sum := sum + a[i] b[j], once j is the index of the term
  have add : ∀ j : ℕ, j < p → convTerm p A B r i = A.getD i 0 * B.getD j 0 →
      Ends lim P d (.set Acc (((Light.Expr.op Light.Op.add) (v Acc)
                                ((Light.Expr.op Light.Op.mul)
                                  (M ((Light.Expr.op Light.Op.add) (v ArgA) (v Idx)))
                                  (M ((Light.Expr.op Light.Op.add) (v ArgB) (v Jdx)))))))
        ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, j], μ⟩ 12 fun σ' => ∃ t',
          σ' = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i + convTerm p A B r i, t'],
            μ⟩ := by
    intro j hj hc
    have hreadB : μ (b + j) = B.getD j 0 := opB.read hj
    rw [hc] at hterm hsum ⊢
    generalize A.getD i 0 = x at hreadA hterm hsum
    generalize B.getD j 0 = y at hreadB hterm hsum
    exact Ends.setTo _ ⟨j, rfl⟩ (by (((try have := Light.Std.space_le (by assumption)));
                                          ((try have := Light.Std.const_le (by assumption)));
                                          (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadA, hreadB] <;> omega)))
  -- if i ≤ r then j := r - i else j := r + p - i
  refine Ends.next 12 (Ends.iteLast (fun hc => ?_) fun hc => ?_)
  · have hir : i ≤ r := by simpa using hc
    exact Ends.setTo (r - i : ℕ) (add _ (by omega) (by rw [convTerm, if_pos hir]))
  · have hir : ¬ i ≤ r := by simpa using hc
    exact Ends.setTo (r + p - i : ℕ) (add _ (by omega) (by rw [convTerm, if_neg hir]))

open Cconv in
/-- **One entry of cconv**, in at most 32 p + 8 steps. -/
theorem cconvEntry_spec (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (hr : r < p) (i₀ s₀ t₀ : ℤ) :
    Ends lim P d cconvEntry ⟨frame [dst, a, b, p, r, i₀, s₀, t₀], μ⟩ (32 * p + 8) fun σ' =>
      ∃ t, σ' = ⟨frame [dst, a, b, p, r, p, convPartialSum p A B r p, t], μ⟩ := by
  have room := pre.room
  -- sum := 0
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
            -- for i < p: one term
            
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
  -- for i < p: one term
  refine Ends.for (fun i σ => ∃ t, σ = ⟨frame [dst, a, b, p, r, i, convPartialSum p A B r i, t], μ⟩)
      p 24
    ⟨t₀, by simp [update_frame_setLocal, convPartialSum]⟩ ?round ?done ?bound
  case bound =>
    rintro i _ - - ⟨t, rfl⟩
    simp
  case round =>
    rintro i _ hi - ⟨t, rfl⟩
    refine (cconvTerm_spec hw pre hr hi t).mono le_rfl ?_
    rintro _ ⟨t', rfl⟩
    exact ⟨by simp, t', by simp [update_frame_setLocal]⟩
  case done => exact fun _ _ h => h








open Cconv in
/-- **cconv** writes the cyclic convolution to dst and changes nothing else, in at most
32 p² + 21 p + 6 steps. -/
theorem cconv_spec (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (spaceDst : dst + p ≤ lim.space) (apartA : dst + p ≤ a ∨ a + p ≤ dst)
    (apartB : dst + p ≤ b ∨ b + p ≤ dst) :
    Ends lim P d cconvBody ⟨frame [dst, a, b, p], μ⟩ (32 * p * p + 21 * p + 6) fun σ' =>
      Seg σ'.mem dst (cconv p A B) ∧ SameOutside μ σ'.mem dst p := by
  have room := pre.room
  -- for r < p
  refine Ends.for (CconvInv μ dst a b p A B) p (32 * p + 13) ?start ?round ?done ?bound
  case start =>
    exact ⟨0, 0, 0, μ, congrArg (fun loc => (⟨loc, μ⟩ : State))
      ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 3).symm),
      fun e he => absurd he (by omega), .refl⟩
  case bound =>
    rintro r _ - - ⟨i, s, t, μ', rfl, -, -⟩
    simp
  case round =>
    rintro r _ hr - ⟨i, s, t, μ', rfl, filled, rest⟩
    have pre' : CconvPre lim μ' a b p α β A B :=
      { pre with
        opA := pre.opA.keep, opB := pre.opB.keep }
    -- sum := the entry number r
    focus
      (repeat
          with_unfolding_none
            first
            | refine Light.Ends.seqAssoc ?_
            | refine Light.Ends.skipThen ?_);
      (first
        | refine Light.Ends.pieceThen (cconvEntry_spec hw pre' hr i s t) ?_ ?_
        | refine Light.Ends.pieceLast (cconvEntry_spec hw pre' hr i s t) ?_ ?_);
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
          rintro _
            ⟨t', rfl⟩
                -- dst[r] := sum
                )
    -- dst[r] := sum
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (dst + r) (convPartialSum p A B r p) ?_ ?_ ?_);
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
    refine ⟨by simp, p, convPartialSum p A B r p, t',
      Function.update μ' (dst + r) (convPartialSum p A B r p), by simp [update_frame_setLocal],
      fun e he => ?_, rest.update ⟨by omega, by omega⟩ _⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (filled e he)
    · exact Function.update_self ..
  case done =>
    rintro _ - ⟨i, s, t, μ', rfl, filled, rest⟩
    refine ⟨fun e he => ?_, rest⟩
    have he' : e < p := by simpa [cconv_eq_map_convPartialSum] using he
    simpa [cconv_eq_map_convPartialSum] using filled e he'

/-- **cconv** as a procedure. -/
theorem cconv_meets {pCconv : ℕ} (hP : P[pCconv]? = some cconvBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (pre : CconvPre lim μ a b p α β A B)
    (spaceDst : dst + p ≤ lim.space := by first
                                            | omega
                                            |
                                              (((try have := Light.Std.space_le (by assumption)));
                                                ((try have := Light.Std.const_le (by assumption)));
                                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (apartA : dst + p ≤ a ∨ a + p ≤ dst := by first
                                                    | omega
                                                    |
                                                      (((try have := Light.Std.space_le (by assumption)));
                                                        ((try have := Light.Std.const_le (by assumption)));
                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (apartB : dst + p ≤ b ∨ b + p ≤ dst := by first
                                                    | omega
                                                    |
                                                      (((try have := Light.Std.space_le (by assumption)));
                                                        ((try have := Light.Std.const_le (by assumption)));
                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) :
    Meets lim P pCconv d [dst, a, b, p] μ (32 * p * p + 21 * p + 6) fun _ μ' =>
      Seg μ' dst (cconv p A B) ∧ SameOutside μ μ' dst p :=
  Meets.of_body hP (cconv_spec hw pre spaceDst apartA apartB)

end cconv

end Light.Sec3

end
end

section


/-!
# Strassen's algorithm in seven uniform phases: the pure side

An entry of a matrix is a vector of `p` numbers, an element of the ring ℤ[x]/(x^p - 1), whose
product is `cconv p`; `vlinList s A B` is the list `A + s B`, which the routine vlin writes.  The
routine for Strassen's algorithm clears the four quarters of the result and then runs seven
phases.  A phase forms `S = A₁ + s_A A₂`, `T = B₁ + s_B B₂`, `M = S · T` (recursively) and adds
`s₁ M` and `s₂ M` to two quarters of the result; the signs are 1, -1 or 0.  This file has the facts
about lists that the proof about the routine uses:

* lengths (`length_vlinList`, `length_quarter`, `length_strassenList`);
* magnitudes: for operands bounded by `α` and `β`, all numbers that are formed at level `j` are
  bounded by `strassenBound p j α β = 16^j p α β` (`absLe_strassenList`);
* the seven phases give `strassenList` (`strassenList_succ_eq_phases`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The list that vlin writes is as long as its operands. -/
theorem length_vlinList (s : ℤ) {A B : List ℤ} {n : ℕ} (hA : A.length = n) (hB : B.length = n) :
    (vlinList s A B).length = n := by
  simp [vlinList, hA, hB]

/-- With the sign 0 the first operand is kept. -/
theorem vlinList_zero {A B : List ℤ} (h : A.length = B.length) : vlinList 0 A B = A := by
  apply List.ext_getElem
  · simp [vlinList, h]
  · intro i h1 h2
    simp [vlinList]

/-- With the sign 0 and twice the same operand, the operand is kept. -/
theorem vlinList_zero_self (A : List ℤ) : vlinList 0 A A = A := vlinList_zero rfl

/-- Adding a list to zeros gives the list. -/
theorem vlinList_zeros_left {q : ℕ} {B : List ℤ} (h : B.length = q) :
    vlinList 1 (zeros q) B = B := by
  apply List.ext_getElem
  · simp [vlinList, zeros, h]
  · intro i h1 h2
    simp [vlinList, zeros]

/-- The bounds of the two operands add up. -/
theorem _root_.ThreeSumApsp.AbsLe.vlinList {s a b : ℤ} {A B : List ℤ} (hA : AbsLe A a)
    (hB : AbsLe B b)
    (hs : |s| ≤ 1) : AbsLe (vlinList s A B) (a + b) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hiA : i < A.length := by simp only [Sec3.vlinList, List.length_zipWith] at hi; omega
  have hiB : i < B.length := by simp only [Sec3.vlinList, List.length_zipWith] at hi; omega
  simp only [Sec3.vlinList, List.getElem_zipWith]
  have hsy : |s * B[i]| ≤ b := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (hB.getElem hiB)
  exact le_trans (abs_add_le _ _) (add_le_add (hA.getElem hiA) hsy)

/-- A larger bound. -/
theorem _root_.ThreeSumApsp.AbsLe.trans_le {l : List ℤ} {a b : ℤ} (h : AbsLe l a) (hab : a ≤ b) :
    AbsLe l b := fun x hx => (h x hx).trans hab

/-- Zeros are bounded by 0. -/
theorem absLe_zeros (q : ℕ) : AbsLe (zeros q) 0 := by
  intro x hx
  simp only [zeros, List.mem_replicate] at hx
  simp [hx.2]

/-- A quarter of a list of 4 q numbers has q numbers. -/
theorem length_quarter {q t : ℕ} {l : List ℤ} (h : l.length = 4 * q) (ht : t < 4) :
    (quarter q t l).length = q := by
  have h1 : (t + 1) * q ≤ 4 * q := Nat.mul_le_mul_right q (by omega)
  have h2 : (t + 1) * q = t * q + q := by ring
  rw [quarter, List.length_take, List.length_drop, h]
  omega

/-- A bound for a list is a bound for its quarters. -/
theorem _root_.ThreeSumApsp.AbsLe.quarter {q t : ℕ} {l : List ℤ} {a : ℤ} (h : AbsLe l a) :
    AbsLe (quarter q t l) a :=
  fun x hx => h x (List.mem_of_mem_drop (List.mem_of_mem_take hx))






/-- A quarter of an array of 4 q numbers is an array of q numbers. -/
theorem _root_.Light.ArrayAt.quarter {μ : ℕ → ℤ} {a q t top : ℕ} {l : List ℤ} {U : ℤ}
    (h : ArrayAt μ a l (4 * q) U top) (ht : t < 4) :
    ArrayAt μ (a + t * q) (quarter q t l) q U top :=
  h.drop_take (Nat.mul_add_le_mul ht le_rfl)

/-- The list A + s B, once it stands at dst, is an array, and the bounds of A and B add up. -/
theorem _root_.Light.ArrayAt.vlinList {μ μ' : ℕ → ℤ} {a dst n top top' : ℕ} {A B : List ℤ}
    {s U V W : ℤ} (hA : ArrayAt μ a A n U top) (lenB : B.length = n) (leB : AbsLe B V)
    (hs : |s| ≤ 1) (seg : Seg μ' dst (vlinList s A B)) (hW : U + V ≤ W := by first
                                                                                  | omega
                                                                                  |
                                                                                    (((try have := Light.Std.space_le (by assumption)));
                                                                                      ((try have := Light.Std.const_le (by assumption)));
                                                                                      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (below : dst + n ≤ top' := by first
                                    | omega
                                    |
                                      (((try have := Light.Std.space_le (by assumption)));
                                        ((try have := Light.Std.const_le (by assumption)));
                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) : ArrayAt μ' dst (vlinList s A B) n W top' :=
  { len := length_vlinList s hA.len lenB, seg, bound := (hA.bound.vlinList leB hs).trans_le hW
    below }

/-- A product in the ring has p numbers. -/
theorem length_cconv (p : ℕ) (A B : List ℤ) : (cconv p A B).length = p := by simp [cconv]

/-- The product of two matrices of 4^j vectors has 4^j vectors. -/
theorem length_strassenList (p : ℕ) :
    ∀ (j : ℕ) (A B : List ℤ), A.length = 4 ^ j * p → B.length = 4 ^ j * p →
      (strassenList p j A B).length = 4 ^ j * p
  | 0, A, B, _, _ => by simp [strassenList, length_cconv]
  | j + 1, A, B, hA, hB => by
    have hA' : A.length = 4 * (4 ^ j * p) := by rw [hA]; ring
    have hB' : B.length = 4 * (4 ^ j * p) := by rw [hB]; ring
    have qa : ∀ t < 4, (quarter (4 ^ j * p) t A).length = 4 ^ j * p :=
      fun t ht => length_quarter hA' ht
    have qb : ∀ t < 4, (quarter (4 ^ j * p) t B).length = 4 ^ j * p :=
      fun t ht => length_quarter hB' ht
    have hs : ∀ X Y : List ℤ, X.length = 4 ^ j * p → Y.length = 4 ^ j * p →
        (strassenList p j X Y).length = 4 ^ j * p := length_strassenList p j
    have ha : ∀ X Y : List ℤ, X.length = 4 ^ j * p → Y.length = 4 ^ j * p →
        (vadd X Y).length = 4 ^ j * p :=
      fun X Y hX hY => by simp [vadd, hX, hY]
    have hb : ∀ X Y : List ℤ, X.length = 4 ^ j * p → Y.length = 4 ^ j * p →
        (vsub X Y).length = 4 ^ j * p :=
      fun X Y hX hY => by simp [vsub, hX, hY]
    simp only [strassenList, List.length_append]
    rw [ha, ha, ha, ha]
    · ring
    all_goals
      repeat' first
        | apply ha | apply hb | apply hs | exact qa _ (by omega) | exact qb _ (by omega)









/-- The bound is not negative. -/
theorem strassenBound_nonneg {p j : ℕ} {α β : ℤ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ strassenBound p j α β := by
  unfold strassenBound
  positivity

/-- The bound of level j + 1 in terms of the bound of level j, for operands that are sums of two. -/
theorem strassenBound_succ (p j : ℕ) (α β : ℤ) :
    strassenBound p (j + 1) α β = 4 * strassenBound p j (2 * α) (2 * β) := by
  unfold strassenBound
  ring

/-- The bound on the entries of the product of two matrices of zeros and ones. -/
theorem strassenBound_one_one (p K : ℕ) : strassenBound p K 1 1 = ((16 ^ K * p : ℕ) : ℤ) := by
  unfold strassenBound
  push_cast
  ring

/-- The bound is at least the bound α for the first operand. -/
theorem le_strassenBound_left {p j : ℕ} {α β : ℤ} (hp : 1 ≤ p) (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    α ≤ strassenBound p j α β := by
  have hpow : (1 : ℤ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hα0 : 0 ≤ α := by omega
  calc α = 1 * (1 * α * 1) := by ring
    _ ≤ 16 ^ j * (p * α * β) := by gcongr

/-- The bound is at least the bound β for the second operand. -/
theorem le_strassenBound_right {p j : ℕ} {α β : ℤ} (hp : 1 ≤ p) (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    β ≤ strassenBound p j α β := by
  have hpow : (1 : ℤ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hβ0 : 0 ≤ β := by omega
  calc β = 1 * (1 * 1 * β) := by ring
    _ ≤ 16 ^ j * (p * α * β) := by gcongr

/-- A product in the ring is bounded by p α β. -/
theorem absLe_cconv {p : ℕ} {A B : List ℤ} {α β : ℤ} (leA : AbsLe A α) (leB : AbsLe B β)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : AbsLe (cconv p A B) (p * α * β) := by
  intro x hx
  rw [cconv_eq_map_convPartialSum] at hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
  have := abs_convPartialSum_le (p := p) leA leB hα hβ r p
  rwa [← mul_assoc] at this

/-- The entries of a sum. -/
theorem _root_.ThreeSumApsp.AbsLe.vadd {X Y : List ℤ} {x y : ℤ} (hX : AbsLe X x) (hY : AbsLe Y y) :
    AbsLe (vadd X Y) (x + y) := by
  rw [← vlinList_one]
  exact hX.vlinList hY (by simp)

/-- The entries of a difference. -/
theorem _root_.ThreeSumApsp.AbsLe.vsub {X Y : List ℤ} {x y : ℤ} (hX : AbsLe X x) (hY : AbsLe Y y) :
    AbsLe (vsub X Y) (x + y) := by
  rw [← vlinList_neg_one]
  exact hX.vlinList hY (by simp)

/-- The entries of a sum of two lists with the same bound. -/
theorem _root_.ThreeSumApsp.AbsLe.vadd_self {X Y : List ℤ} {c : ℤ} (hX : AbsLe X c)
    (hY : AbsLe Y c) :
    AbsLe (vadd X Y) (2 * c) :=
  (hX.vadd hY).trans_le (by omega)

/-- The entries of a difference of two lists with the same bound. -/
theorem _root_.ThreeSumApsp.AbsLe.vsub_self {X Y : List ℤ} {c : ℤ} (hX : AbsLe X c)
    (hY : AbsLe Y c) :
    AbsLe (vsub X Y) (2 * c) :=
  (hX.vsub hY).trans_le (by omega)

/-- The entries of the result of the routine, and of the products of its phases, are bounded. -/
theorem absLe_strassenList (p : ℕ) :
    ∀ (j : ℕ) (A B : List ℤ) (α β : ℤ), AbsLe A α → AbsLe B β → 0 ≤ α → 0 ≤ β →
      AbsLe (strassenList p j A B) (strassenBound p j α β)
  | 0, A, B, α, β, leA, leB, hα, hβ => by
    simpa [strassenList, strassenBound] using absLe_cconv (p := p) leA leB hα hβ
  | j + 1, A, B, α, β, leA, leB, hα, hβ => by
    have ih : ∀ X Y : List ℤ, AbsLe X (2 * α) → AbsLe Y (2 * β) →
        AbsLe (strassenList p j X Y) (strassenBound p j (2 * α) (2 * β)) := fun X Y hX hY =>
      absLe_strassenList p j X Y _ _ hX hY (by omega) (by omega)
    have qa : ∀ t, AbsLe (quarter (4 ^ j * p) t A) α := fun t => leA.quarter
    have qb : ∀ t, AbsLe (quarter (4 ^ j * p) t B) β := fun t => leB.quarter
    have qa2 : ∀ t, AbsLe (quarter (4 ^ j * p) t A) (2 * α) := fun t => (qa t).trans_le (by omega)
    have qb2 : ∀ t, AbsLe (quarter (4 ^ j * p) t B) (2 * β) := fun t => (qb t).trans_le (by omega)
    -- the seven products of Strassen's algorithm
    have m1 := ih _ _ ((qa 0).vadd_self (qa 3)) ((qb 0).vadd_self (qb 3))
    have m2 := ih _ _ ((qa 2).vadd_self (qa 3)) (qb2 0)
    have m3 := ih _ _ (qa2 0) ((qb 1).vsub_self (qb 3))
    have m4 := ih _ _ (qa2 3) ((qb 2).vsub_self (qb 0))
    have m5 := ih _ _ ((qa 0).vadd_self (qa 1)) (qb2 3)
    have m6 := ih _ _ ((qa 2).vsub_self (qa 0)) ((qb 0).vadd_self (qb 1))
    have m7 := ih _ _ ((qa 1).vsub_self (qa 3)) ((qb 2).vadd_self (qb 3))
    have hR : 0 ≤ strassenBound p j (2 * α) (2 * β) :=
      strassenBound_nonneg (by omega) (by omega)
    rw [strassenBound_succ]
    simp only [strassenList]
    intro x hx
    simp only [List.mem_append] at hx
    -- each quadrant of the result is a sum of at most four of them
    rcases hx with ((hx | hx) | hx) | hx
    · exact (((m1.vadd m4).vsub m5).vadd m7).trans_le (by omega) x hx
    · exact (m3.vadd m5).trans_le (by omega) x hx
    · exact (m2.vadd m4).trans_le (by omega) x hx
    · exact (((m1.vsub m2).vadd m3).vadd m6).trans_le (by omega) x hx

/-- The product of a phase on quarters of the operands has the length of a quarter. -/
theorem length_phaseM_quarter {p j : ℕ} {A B : List ℤ} (hA : A.length = 4 * (4 ^ j * p))
    (hB : B.length = 4 * (4 ^ j * p)) (sA sB : ℤ) {t1 t2 t3 t4 : ℕ}
    (ht : t1 < 4 ∧ t2 < 4 ∧ t3 < 4 ∧ t4 < 4 := by omega) :
    (phaseM p j sA (quarter (4 ^ j * p) t1 A) (quarter (4 ^ j * p) t2 A) sB
      (quarter (4 ^ j * p) t3 B) (quarter (4 ^ j * p) t4 B)).length = 4 ^ j * p := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  exact length_strassenList p j _ _
    (length_vlinList _ (length_quarter hA h1) (length_quarter hA h2))
    (length_vlinList _ (length_quarter hB h3) (length_quarter hB h4))

/-- **The seven phases give Strassen's algorithm.** -/
theorem strassenList_succ_eq_phases (p j : ℕ) (A B : List ℤ) (hA : A.length = 4 ^ (j + 1) * p)
    (hB : B.length = 4 ^ (j + 1) * p) :
    let q := 4 ^ j * p
    let a := fun t => quarter q t A
    let b := fun t => quarter q t B
    let m1 := phaseM p j 1 (a 0) (a 3) 1 (b 0) (b 3)
    let m2 := phaseM p j 1 (a 2) (a 3) 0 (b 0) (b 0)
    let m3 := phaseM p j 0 (a 0) (a 0) (-1) (b 1) (b 3)
    let m4 := phaseM p j 0 (a 3) (a 3) (-1) (b 2) (b 0)
    let m5 := phaseM p j 1 (a 0) (a 1) 0 (b 3) (b 3)
    let m6 := phaseM p j (-1) (a 2) (a 0) 1 (b 0) (b 1)
    let m7 := phaseM p j (-1) (a 1) (a 3) 1 (b 2) (b 3)
    strassenList p (j + 1) A B
      = vlinList 1 (vlinList 0 (vlinList (-1) (vlinList 1 (vlinList 1 (zeros q) m1) m4) m5) m6) m7
        ++ vlinList 1 (vlinList 1 (zeros q) m3) m5
        ++ vlinList 1 (vlinList 1 (zeros q) m2) m4
        ++ vlinList 0 (vlinList 1 (vlinList 1 (vlinList (-1) (vlinList 1 (zeros q) m1) m2) m3) m6)
          m7 := by
  intro q a b m1 m2 m3 m4 m5 m6 m7
  have hA' : A.length = 4 * q := by rw [hA]; ring
  have hB' : B.length = 4 * q := by rw [hB]; ring
  have len1 : m1.length = q := length_phaseM_quarter hA' hB' _ _
  have len2 : m2.length = q := length_phaseM_quarter hA' hB' _ _
  have len3 : m3.length = q := length_phaseM_quarter hA' hB' _ _
  have len4 : m4.length = q := length_phaseM_quarter hA' hB' _ _
  have len5 : m5.length = q := length_phaseM_quarter hA' hB' _ _
  have len6 : m6.length = q := length_phaseM_quarter hA' hB' _ _
  have len7 : m7.length = q := length_phaseM_quarter hA' hB' _ _
  rw [vlinList_zeros_left len1, vlinList_zeros_left len3, vlinList_zeros_left len2,
    vlinList_zero (A := vlinList (-1) (vlinList 1 m1 m4) m5) (B := m6)
      (by rw [length_vlinList _ (length_vlinList _ len1 len4) len5, len6]),
    vlinList_zero (A := vlinList 1 (vlinList 1 (vlinList (-1) m1 m2) m3) m6) (B := m7)
      (by rw [length_vlinList _ (length_vlinList _ (length_vlinList _ len1 len2) len3) len6, len7])]
  simp only [m1, m2, m3, m4, m5, m6, m7, phaseM, vlinList_one, vlinList_neg_one, vlinList_zero_self]
  rfl

end Light.Sec3

end
end

section


/-!
# Strassen's algorithm for matrices over ℤ[x]/(x^p - 1) in Z-order

"Computing PQ takes […] O(n^{log₂ 7}) with Strassen's algorithm" (proof of Theorem 17).

strassen(dst, a, b, j, szt, p, scr): dst := a · b for 2^j × 2^j matrices whose entries are vectors
of p numbers, stored in Z-order, so that the four quadrants of a matrix are the four quarters of its
segment.  szt is the address of the table of the sizes 4^i p, and scr is scratch space.

* At level 0 the product is one product in the ring (`strassen_zero`).
* At level j + 1 the routine clears dst and runs seven phases (`strassen_succ`).  phase(a1, a2, sA,
  b1, b2, sB, c1, s1, c2, s2, j, szt, p, scr, q) forms S = a1 + sA a2 and T = b1 + sB b2 in the
  scratch space, M = S · T by a recursive call, and adds s1 M to c1 and s2 M to c2 (`phase_meets`).
* Between two phases the four quarters of dst hold four lists, and the operands and the table are in
  place (`StrInv`); a phase changes two of the lists (`phase_step`).  After the seven phases the
  four lists are the four quadrants of the product (`sevenPhases_spec`).
* `strassen_spec` is the induction on the level: the product stands at dst after at most
  `strSteps p j` steps, and nothing has changed outside dst and `strScr p j` cells of scratch space.
  The recursion `strSteps` is bounded where the running times are added up.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/









namespace Phase




















end Phase






















namespace Str

















end Str
























































/-! ## The specification -/













variable {lim : Limits} {P : Program} {d : ℕ}




























/-- What strassen assumes still holds when no cell below dst has changed. -/
theorem StrPre.keep {μ μ' : ℕ → ℤ} {j : ℕ} {x : StrArgs} (pre : StrPre lim μ j x)
    (hs : Kept μ μ' x.dst := by ((try refine Light.SameOn.cell ?_);
                                    (intro apspMacro_157694_0 apspMacro_157694_1);
                                    (first
                                      |
                                        ((((repeat
                                                  (((with_reducible
                                                          rename Light.SameOn _ _ _ => apspMacro_157694_2));
                                                    ((try
                                                          have :=
                                                            apspMacro_157694_2 apspMacro_157694_0 (by omega)));
                                                    (revert apspMacro_157694_2)));
                                              (intros);
                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                          (omega))
                                      |
                                        ((simp [] at apspMacro_157694_1);
                                          (((repeat
                                                  (((with_reducible
                                                          rename Light.SameOn _ _ _ => apspMacro_157694_3));
                                                    ((try
                                                          have :=
                                                            apspMacro_157694_3 apspMacro_157694_0 (by omega)));
                                                    (revert apspMacro_157694_3)));
                                              (intros);
                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                          (omega))
                                      |
                                        ((((repeat
                                                  (((with_reducible
                                                          rename Light.SameOn _ _ _ => apspMacro_157694_4));
                                                    ((try
                                                          have :=
                                                            apspMacro_157694_4 apspMacro_157694_0 (by omega)));
                                                    (revert apspMacro_157694_4)));
                                              (intros);
                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                          (fail
                                              "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                        its condition K x does not follow from the hypotheses."))))) : StrPre lim μ' j x :=
  { pre with opA := pre.opA.keep, opB := pre.opB.keep, table := pre.table.keep }








/-! ## A phase -/










namespace PhaseArgs

variable (x : PhaseArgs) (j : ℕ)





















end PhaseArgs
































section phase

variable {ν : StrNums} {μ μ' : ℕ → ℤ} {j : ℕ} {x : PhaseArgs}

namespace PhasePre

/-- The product of a phase has q numbers. -/
theorem length_prod (pre : PhasePre lim μ j x) : (x.prod j).length = x.q := by
  have hq := pre.size
  rw [hq]
  exact length_strassenList x.p j _ _ (hq ▸ length_vlinList _ pre.opA1.len pre.opA2.len)
    (hq ▸ length_vlinList _ pre.opB1.len pre.opB2.len)

/-- The bound of level j for operands that are sums of two is not negative. -/
theorem bound_nonneg (pre : PhasePre lim μ j x) :
    0 ≤ strassenBound x.p j (2 * x.α) (2 * x.β) :=
  strassenBound_nonneg (by have := pre.oneA; omega) (by have := pre.oneB; omega)

/-- The product of a phase is bounded by strassenBound p j (2 α) (2 β). -/
theorem absLe_prod (pre : PhasePre lim μ j x) :
    AbsLe (x.prod j) (strassenBound x.p j (2 * x.α) (2 * x.β)) := by
  have hα := pre.oneA
  have hβ := pre.oneB
  exact absLe_strassenList x.p j _ _ (2 * x.α) (2 * x.β)
    ((pre.opA1.bound.vlinList pre.opA2.bound pre.signA).trans_le (by omega))
    ((pre.opB1.bound.vlinList pre.opB2.bound pre.signB).trans_le (by omega)) (by omega) (by omega)

/-- The scratch space of level j + 1: three lists of q numbers, and the scratch space of level j. -/
theorem space_inner (pre : PhasePre lim μ j x) : x.scr + (3 * x.q + strScr x.p j) ≤ lim.space := by
  have := pre.space
  rwa [strScr, ← pre.size] at this

/-- What a phase assumes still holds when no cell below scr has changed. -/
theorem keep (pre : PhasePre lim μ j x) (hs : Kept μ μ' x.scr := by ((try refine Light.SameOn.cell ?_);
                                                                         (intro apspMacro_159540_0 apspMacro_159540_1);
                                                                         (first
                                                                           |
                                                                             ((((repeat
                                                                                       (((with_reducible
                                                                                               rename Light.SameOn _ _ _ => apspMacro_159540_2));
                                                                                         ((try
                                                                                               have :=
                                                                                                 apspMacro_159540_2 apspMacro_159540_0 (by omega)));
                                                                                         (revert apspMacro_159540_2)));
                                                                                   (intros);
                                                                                   (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                               (omega))
                                                                           |
                                                                             ((simp [] at apspMacro_159540_1);
                                                                               (((repeat
                                                                                       (((with_reducible
                                                                                               rename Light.SameOn _ _ _ => apspMacro_159540_3));
                                                                                         ((try
                                                                                               have :=
                                                                                                 apspMacro_159540_3 apspMacro_159540_0 (by omega)));
                                                                                         (revert apspMacro_159540_3)));
                                                                                   (intros);
                                                                                   (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                               (omega))
                                                                           |
                                                                             ((((repeat
                                                                                       (((with_reducible
                                                                                               rename Light.SameOn _ _ _ => apspMacro_159540_4));
                                                                                         ((try
                                                                                               have :=
                                                                                                 apspMacro_159540_4 apspMacro_159540_0 (by omega)));
                                                                                         (revert apspMacro_159540_4)));
                                                                                   (intros);
                                                                                   (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                               (fail
                                                                                   "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                             SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                             its condition K x does not follow from the hypotheses."))))) :
    PhasePre lim μ' j x :=
  { pre with
    opA1 := pre.opA1.keep, opA2 := pre.opA2.keep, opB1 := pre.opB1.keep, opB2 := pre.opB2.keep
    out1 := pre.out1.keep, out2 := pre.out2.keep, table := pre.table.keep }

/-- What the recursive call of a phase assumes, once the two operands stand in the scratch space. -/
theorem inner (pre : PhasePre lim μ j x) (segS : Seg μ x.scr x.S)
    (segT : Seg μ (x.scr + x.q) x.T) : StrPre lim μ j x.inner := by
  have hB4 := strassenBound_succ x.p j x.α x.β
  have hB0 := pre.bound_nonneg
  have space := pre.space_inner
  (obtain ⟨⟩ := id pre)
  exact
    { size := pre.size, prime := pre.prime, table := pre.table.mono
      opA := pre.opA1.vlinList pre.opA2.len pre.opA2.bound pre.signA segS
      opB := pre.opB1.vlinList pre.opB2.len pre.opB2.bound pre.signB segT }

end PhasePre

variable (prog : StrProg P ν) (hw : (lim.space : ℤ) ≤ lim.word)
include prog hw

/-- **The operands of a phase.** -/
theorem phaseOpnds_spec (pre : PhasePre lim μ j x) (hd : d < lim.depth) :
    Ends lim P d (phaseOpnds ν) ⟨frame (x.vals j), μ⟩ (46 * x.q + 28) fun σ' =>
      ∃ (r : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (x.vals j ++ [r]), μ'⟩ ∧
        Seg μ' x.scr x.S ∧ Seg μ' (x.scr + x.q) x.T ∧ SameOutside μ μ' x.scr (2 * x.q) := by
  have space := pre.space_inner
  have word := pre.word
  have hleα := le_strassenBound_left (j := j + 1) pre.prime pre.oneA pre.oneB
  have hleβ := le_strassenBound_right (j := j + 1) pre.prime pre.oneA pre.oneB
  have lenS := length_vlinList x.sA pre.opA1.len pre.opA2.len
  ((obtain ⟨⟩ := id pre.opA1); (obtain ⟨⟩ := id pre.opA2);
    (obtain ⟨⟩ := id pre.opB1); (obtain ⟨⟩ := id pre.opB2))
  -- S := a1 + sA a2
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
            ((vlin_meets prog.vlin hw (dst := x.scr) (V := x.α)
                { opA := pre.opA1.mono, opB := pre.opA2.mono, sign := pre.signA })
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (vlin_meets prog.vlin hw (dst := x.scr) (V := x.α)
              { opA := pre.opA1.mono, opB := pre.opA2.mono, sign := pre.signA })
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
        ((rintro _ μ₁
              ⟨segS, rest₁⟩
                  -- T := b1 + sB b2
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- T := b1 + sB b2
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
            ((vlin_meets prog.vlin hw (dst := x.scr + x.q) (V := x.β)
                { opA := pre.opB1.keep.mono, opB := pre.opB2.keep.mono,
                  sign := pre.signB })
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (vlin_meets prog.vlin hw (dst := x.scr + x.q) (V := x.β)
              { opA := pre.opB1.keep.mono, opB := pre.opB2.keep.mono,
                sign := pre.signB })
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
        ((rintro r μ₂ ⟨segT, rest₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨r, μ₂, rfl, segS.keep, segT, by ((try refine Light.SameOn.cell ?_);
                                                (intro apspMacro_161621_0 apspMacro_161621_1);
                                                (first
                                                  |
                                                    ((((repeat
                                                              (((with_reducible
                                                                      rename Light.SameOn _ _ _ => apspMacro_161621_2));
                                                                ((try
                                                                      have :=
                                                                        apspMacro_161621_2 apspMacro_161621_0 (by omega)));
                                                                (revert apspMacro_161621_2)));
                                                          (intros);
                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                      (omega))
                                                  |
                                                    ((simp [] at apspMacro_161621_1);
                                                      (((repeat
                                                              (((with_reducible
                                                                      rename Light.SameOn _ _ _ => apspMacro_161621_3));
                                                                ((try
                                                                      have :=
                                                                        apspMacro_161621_3 apspMacro_161621_0 (by omega)));
                                                                (revert apspMacro_161621_3)));
                                                          (intros);
                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                      (omega))
                                                  |
                                                    ((((repeat
                                                              (((with_reducible
                                                                      rename Light.SameOn _ _ _ => apspMacro_161621_4));
                                                                ((try
                                                                      have :=
                                                                        apspMacro_161621_4 apspMacro_161621_0 (by omega)));
                                                                (revert apspMacro_161621_4)));
                                                          (intros);
                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                      (fail
                                                          "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                    SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                    its condition K x does not follow from the hypotheses."))))⟩

/-- **The end of a phase.** -/
theorem phaseAccum_spec (pre : PhasePre lim μ j x) (segM : Seg μ (x.scr + x.q + x.q) (x.prod j))
    (hd : d < lim.depth) (r : ℤ) :
    Ends lim P d (phaseAccum ν) ⟨frame (x.vals j ++ [r]), μ⟩ (46 * x.q + 34) fun σ' =>
      Seg σ'.mem x.c1 (vlinList x.s1 x.C1 (x.prod j)) ∧
        Seg σ'.mem x.c2 (vlinList x.s2 x.C2 (x.prod j)) ∧
        SameOutside2 μ σ'.mem x.c1 x.q x.c2 x.q := by
  have space := pre.space_inner
  have word := pre.word
  have apart := pre.apart
  have hB4 := strassenBound_succ x.p j x.α x.β
  have hB0 := pre.bound_nonneg
  have len1 := length_vlinList x.s1 pre.out1.len pre.length_prod
  ((obtain ⟨⟩ := id pre.out1); (obtain ⟨⟩ := id pre.out2))
  have opM : ArrayAt μ (x.scr + x.q + x.q) (x.prod j) x.q (2 * strassenBound x.p (j + 1) x.α x.β)
      lim.space :=
    { len := pre.length_prod, seg := segM, bound := pre.absLe_prod.trans_le (by omega) }
  -- c1 := c1 + s1 M
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
            ((vlin_meets prog.vlin hw (dst := x.c1)
                { opA := pre.out1.mono, opB := opM, sign := pre.sign1 })
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (vlin_meets prog.vlin hw (dst := x.c1)
              { opA := pre.out1.mono, opB := opM, sign := pre.sign1 })
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
        ((rintro _ μ₁
              ⟨seg1, rest₁⟩
                  -- c2 := c2 + s2 M
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- c2 := c2 + s2 M
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
            ((vlin_meets prog.vlin hw (dst := x.c2)
                { opA := pre.out2.keep.mono, opB := opM.keep, sign := pre.sign2 })
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (vlin_meets prog.vlin hw (dst := x.c2)
              { opA := pre.out2.keep.mono, opB := opM.keep, sign := pre.sign2 })
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
        ((rintro _ μ₂ ⟨seg2, rest₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨seg1.keep, seg2, by ((try refine Light.SameOn.cell ?_);
                                 (intro apspMacro_162916_0 apspMacro_162916_1);
                                 (first
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_162916_2));
                                                 ((try
                                                       have :=
                                                         apspMacro_162916_2 apspMacro_162916_0 (by omega)));
                                                 (revert apspMacro_162916_2)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((simp [] at apspMacro_162916_1);
                                       (((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_162916_3));
                                                 ((try
                                                       have :=
                                                         apspMacro_162916_3 apspMacro_162916_0 (by omega)));
                                                 (revert apspMacro_162916_3)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_162916_4));
                                                 ((try
                                                       have :=
                                                         apspMacro_162916_4 apspMacro_162916_0 (by omega)));
                                                 (revert apspMacro_162916_4)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (fail
                                           "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                     SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                     its condition K x does not follow from the hypotheses."))))⟩

/-- **A phase** adds s1 M to c1 and s2 M to c2, where M = (a1 + sA a2) · (b1 + sB b2), and changes
nothing else but the scratch space. -/
theorem phase_meets (H : StrSpec lim P ν j) (pre : PhasePre lim μ j x)
    (hd : d + 2 * j + 2 ≤ lim.depth) :
    Meets lim P ν.pPhase d (x.vals j) μ (92 * x.q + 83 + strSteps x.p j) fun _ =>
      PhasePost μ j x := by
  have space := pre.space_inner
  have hscr : strScr x.p (j + 1) = 3 * x.q + strScr x.p j := by rw [strScr, pre.size]
  refine Meets.of_body prog.phase ?_
  -- S := a1 + sA a2; T := b1 + sB b2
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (phaseOpnds_spec prog hw pre (by omega)) ?_ ?_
      |
        refine
          Light.Ends.pieceLast (phaseOpnds_spec prog hw pre (by omega)) ?_ ?_);
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
        rintro _
          ⟨r, μ₁, rfl, segS, segT, rest₁⟩
              -- M := S · T
              )
  -- M := S · T
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
            ((H x.inner μ₁ (pre.keep.inner segS segT) _ (by omega)) _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (H x.inner μ₁ (pre.keep.inner segS segT) _ (by omega)) ?_ ?_ ?_ ?_);
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
        ((rintro r' μ₂ ⟨segM, rest₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  dsimp only [PhaseArgs.inner] at segM rest₂
  -- c1 := c1 + s1 M; c2 := c2 + s2 M
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen
            (phaseAccum_spec prog hw pre.keep segM (by omega) r') ?_ ?_
      |
        refine
          Light.Ends.pieceLast
            (phaseAccum_spec prog hw pre.keep segM (by omega) r') ?_ ?_);
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
    (on_goal -1 => rintro σ' ⟨seg1, seg2, rest₃⟩)
  exact ⟨seg1, seg2, by ((try refine Light.SameOn.cell ?_);
                            (intro apspMacro_163929_0 apspMacro_163929_1);
                            (first
                              |
                                ((((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ => apspMacro_163929_2));
                                            ((try
                                                  have :=
                                                    apspMacro_163929_2 apspMacro_163929_0 (by omega)));
                                            (revert apspMacro_163929_2)));
                                      (intros);
                                      (try simp only [Function.update_apply, Light.wrote] at *)));
                                  (omega))
                              |
                                ((simp [] at apspMacro_163929_1);
                                  (((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ => apspMacro_163929_3));
                                            ((try
                                                  have :=
                                                    apspMacro_163929_3 apspMacro_163929_0 (by omega)));
                                            (revert apspMacro_163929_3)));
                                      (intros);
                                      (try simp only [Function.update_apply, Light.wrote] at *)));
                                  (omega))
                              |
                                ((((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ => apspMacro_163929_4));
                                            ((try
                                                  have :=
                                                    apspMacro_163929_4 apspMacro_163929_0 (by omega)));
                                            (revert apspMacro_163929_4)));
                                      (intros);
                                      (try simp only [Function.update_apply, Light.wrote] at *)));
                                  (fail
                                      "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                its condition K x does not follow from the hypotheses."))))⟩

end phase

/-! ## Between two phases -/















































/-- Two different quarters do not meet. -/
theorem quarter_apart {t t' : ℕ} (q : ℕ) (h : t ≠ t') :
    t * q + q ≤ t' * q ∨ t' * q + q ≤ t * q :=
  (Nat.lt_or_gt_of_ne h).imp (fun h' => Nat.mul_add_le_mul h' le_rfl)
    fun h' => Nat.mul_add_le_mul h' le_rfl

/-- A property of the four lists after two of them have been replaced. -/
theorem forall_update_update {Φ : ℕ → List ℤ → Prop} {L : ℕ → List ℤ} {t₁ t₂ : ℕ}
    {X₁ X₂ : List ℤ} (h : ∀ t < 4, t ≠ t₁ → t ≠ t₂ → Φ t (L t)) (h₁ : Φ t₁ X₁) (h₂ : Φ t₂ X₂) :
    ∀ t < 4, Φ t (Function.update (Function.update L t₁ X₁) t₂ X₂ t) := by
  intro t ht
  by_cases e₂ : t = t₂
  · rw [e₂, Function.update_self]
    exact h₂
  by_cases e₁ : t = t₁
  · rw [Function.update_of_ne e₂, e₁, Function.update_self]
    exact h₁
  · rw [Function.update_of_ne e₂, Function.update_of_ne e₁]
    exact h t ht e₁ e₂

section step

variable {ν : StrNums} {μ μ' : ℕ → ℤ} {j q κ : ℕ} {x : StrArgs} {L : ℕ → List ℤ} {row : PhaseRow}

namespace StrInv

/-- An operand has four quarters. -/
theorem size_eq (inv : StrInv lim μ j q x L κ) : x.len = 4 * q := by
  rw [inv.size, inv.quarterLen]
  ring

/-- What the phase of a row assumes holds between two phases. -/
theorem phasePre (inv : StrInv lim μ j q x L κ) (hκ : κ ≤ 7) (hr : row.Ok) :
    PhasePre lim μ j (x.phase q L row) := by
  have hB0 : 0 ≤ strassenBound x.p j (2 * x.α) (2 * x.β) :=
    strassenBound_nonneg (by have := inv.oneA; omega) (by have := inv.oneB; omega)
  have hbound : (κ : ℤ) * strassenBound x.p j (2 * x.α) (2 * x.β) ≤
      2 * strassenBound x.p (j + 1) x.α x.β := by
    rw [strassenBound_succ]
    calc (κ : ℤ) * strassenBound x.p j (2 * x.α) (2 * x.β)
        ≤ 8 * strassenBound x.p j (2 * x.α) (2 * x.β) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hκ.trans (by norm_num)) hB0
      _ = 2 * (4 * strassenBound x.p j (2 * x.α) (2 * x.β)) := by ring
  have hq := inv.size_eq
  have opA := (hq ▸ inv.opA).mono le_rfl (Nat.le_of_add_right_le inv.dstBelow)
  have opB := (hq ▸ inv.opB).mono le_rfl (Nat.le_of_add_right_le inv.dstBelow)
  have hapart := quarter_apart q hr.ne
  (obtain ⟨⟩ := id inv.toStrPre)
  exact
    { size := inv.quarterLen, prime := inv.prime, table := inv.table.mono
      opA1 := opA.quarter hr.a1, opA2 := opA.quarter hr.a2
      opB1 := opB.quarter hr.b1, opB2 := opB.quarter hr.b2
      out1 := (inv.out _ hr.c1).mono hbound le_rfl, out2 := (inv.out _ hr.c2).mono hbound le_rfl
      signA := hr.sA, signB := hr.sB, sign1 := hr.s1, sign2 := hr.s2
      oneA := inv.oneA, oneB := inv.oneB, word := inv.word, space := inv.space }

/-- The state after a phase: two of the four lists are replaced, the rest is as before. -/
theorem step (inv : StrInv lim μ j q x L κ) (hκ : κ ≤ 7) (hr : row.Ok)
    (post : PhasePost μ j (x.phase q L row) μ') :
    StrInv lim μ' j q x (x.after j q L row) (κ + 1) := by
  have pre := inv.phasePre hκ hr
  have hB0 : 0 ≤ strassenBound x.p j (2 * x.α) (2 * x.β) := pre.bound_nonneg
  have hsucc : ((κ + 1 : ℕ) : ℤ) * strassenBound x.p j (2 * x.α) (2 * x.β) =
      κ * strassenBound x.p j (2 * x.α) (2 * x.β) + strassenBound x.p j (2 * x.α) (2 * x.β) := by
    push_cast
    ring
  have hq := inv.size_eq
  have dstBelow := inv.dstBelow
  have same : SameOutside3 μ μ' (x.dst + row.c1 * q) q (x.dst + row.c2 * q) q x.scr
      (strScr x.p (j + 1)) := post.same
  have pre' : StrPre lim μ' (j + 1) x := inv.toStrPre.keep
  refine
    { toStrPre := pre'
      quarterLen := inv.quarterLen
      out := forall_update_update
        (Φ := fun t X => ArrayAt μ' (x.dst + t * q) X q _ x.scr) (fun t ht e₁ e₂ => ?_)
        ((inv.out _ hr.c1).vlinList pre.length_prod pre.absLe_prod hr.s1 post.out1 hsucc.ge
          pre.out1.below)
        ((inv.out _ hr.c2).vlinList pre.length_prod pre.absLe_prod hr.s2 post.out2 hsucc.ge
          pre.out2.below) }
  · have hapart₁ := quarter_apart q e₁
    have hapart₂ := quarter_apart q e₂
    have hin : t * q + q ≤ 4 * q := Nat.mul_add_le_mul ht le_rfl
    exact (inv.out t ht).keep.mono

end StrInv

/-- **A phase, called from the body of strassen**: with M the product of the row, s1 M is added to
the list number c1 and s2 M to the list number c2. -/
theorem phase_step (prog : StrProg P ν) (hw : (lim.space : ℤ) ≤ lim.word)
    (H : StrSpec lim P ν j) (inv : StrInv lim μ j q x L κ) (hd : d + 2 * j + 2 ≤ lim.depth)
    (row : PhaseRow) (hκ : κ ≤ 7 := by omega)
    (hr : row.Ok := by constructor <;> simp) :
    Meets lim P ν.pPhase d ((x.phase q L row).vals j) μ (92 * q + 83 + strSteps x.p j) fun _ μ' =>
      StrInv lim μ' j q x (x.after j q L row) (κ + 1) ∧
        SameOutside2 μ μ' x.dst (4 * q) x.scr (strScr x.p (j + 1)) := by
  refine (phase_meets prog hw H (inv.phasePre hκ hr) hd).mono le_rfl fun _ μ' post => ?_
  have hin₁ : row.c1 * q + q ≤ 4 * q := Nat.mul_add_le_mul hr.c1 le_rfl
  have hin₂ : row.c2 * q + q ≤ 4 * q := Nat.mul_add_le_mul hr.c2 le_rfl
  have same : SameOutside3 μ μ' (x.dst + row.c1 * q) q (x.dst + row.c2 * q) q x.scr
      (strScr x.p (j + 1)) := post.same
  exact ⟨inv.step hκ hr post, by ((try refine Light.SameOn.cell ?_);
                                      (intro apspMacro_169317_0 apspMacro_169317_1);
                                      (first
                                        |
                                          ((((repeat
                                                    (((with_reducible
                                                            rename Light.SameOn _ _ _ => apspMacro_169317_2));
                                                      ((try
                                                            have :=
                                                              apspMacro_169317_2 apspMacro_169317_0 (by omega)));
                                                      (revert apspMacro_169317_2)));
                                                (intros);
                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                            (omega))
                                        |
                                          ((simp [] at apspMacro_169317_1);
                                            (((repeat
                                                    (((with_reducible
                                                            rename Light.SameOn _ _ _ => apspMacro_169317_3));
                                                      ((try
                                                            have :=
                                                              apspMacro_169317_3 apspMacro_169317_0 (by omega)));
                                                      (revert apspMacro_169317_3)));
                                                (intros);
                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                            (omega))
                                        |
                                          ((((repeat
                                                    (((with_reducible
                                                            rename Light.SameOn _ _ _ => apspMacro_169317_4));
                                                      ((try
                                                            have :=
                                                              apspMacro_169317_4 apspMacro_169317_0 (by omega)));
                                                      (revert apspMacro_169317_4)));
                                                (intros);
                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                            (fail
                                                "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                          its condition K x does not follow from the hypotheses."))))⟩

end step

/-- Four lists of q numbers in the four quarters of a segment are one list. -/
theorem seg_of_quarters {μ : ℕ → ℤ} {dst q : ℕ} {L : ℕ → List ℤ}
    (seg : ∀ t < 4, Seg μ (dst + t * q) (L t)) (len : ∀ t < 4, (L t).length = q) :
    Seg μ dst (L 0 ++ L 1 ++ L 2 ++ L 3) := by
  rw [seg_append, seg_append, seg_append]
  simp only [List.length_append, len 0 (by omega), len 1 (by omega), len 2 (by omega)]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa using seg 0 (by omega)
  · simpa using seg 1 (by omega)
  · rw [show dst + (q + q) = dst + 2 * q by ring]
    exact seg 2 (by omega)
  · rw [show dst + (q + q + q) = dst + 3 * q by ring]
    exact seg 3 (by omega)

/-- A quarter of a cleared segment is cleared. -/
theorem seg_zeros_quarter {μ : ℕ → ℤ} {dst q t : ℕ} (h : Seg μ dst (List.replicate (4 * q) 0))
    (ht : t < 4) : Seg μ (dst + t * q) (zeros q) := by
  intro i hi
  have hi' : i < q := by simpa [zeros] using hi
  have hin : t * q + q ≤ 4 * q := Nat.mul_add_le_mul ht le_rfl
  have hcell := h (t * q + i) (by simp; omega)
  rw [List.getElem_replicate, ← Nat.add_assoc] at hcell
  simpa [zeros] using hcell

/-! ## The seven phases -/

section levels

variable {ν : StrNums} {μ : ℕ → ℤ} {j q : ℕ} {x : StrArgs} (prog : StrProg P ν)
  (hw : (lim.space : ℤ) ≤ lim.word)
include prog hw

/-- **The seven phases** turn four cleared quarters into the product. -/
theorem sevenPhases_spec (H : StrSpec lim P ν j)
    (inv : StrInv lim μ j q x (fun _ => zeros q) 0) (hd : d + 2 * j + 3 ≤ lim.depth)
    (lvl z r : ℤ) :
    Ends lim P d (sevenPhases ν)
      ⟨frame [x.dst, x.a, x.b, lvl, x.szt, x.p, x.scr, q, (2 * q : ℕ), (3 * q : ℕ), j, z, r], μ⟩
      (7 * (92 * q + 123 + strSteps x.p j)) fun σ' =>
        Seg σ'.mem x.dst (strassenList x.p (j + 1) x.A x.B) ∧
        SameOutside2 μ σ'.mem x.dst x.len x.scr (strScr x.p (j + 1)) := by
  have hq := inv.size_eq
  have hd' : d + 1 + 2 * j + 2 ≤ lim.depth := by omega
  ((obtain ⟨⟩ := id inv.toStrPre); (obtain ⟨⟩ := id inv.opA);
    (obtain ⟨⟩ := id inv.opB))
  -- M₁ = (a₀ + a₃) (b₀ + b₃) goes to the quarters 0 and 3
  refine Ends.callToThen (phase_step prog hw H inv hd' ⟨0, 3, 1, 0, 3, 1, 0, 1, 3, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₁ ⟨inv₁, rest₁⟩
  -- M₂ = (a₂ + a₃) b₀ goes to 2 and, with the sign -1, to 3
  refine Ends.callToThen (phase_step prog hw H inv₁ hd' ⟨2, 3, 1, 0, 0, 0, 2, 1, 3, -1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₂ ⟨inv₂, rest₂⟩
  -- M₃ = a₀ (b₁ - b₃) goes to 1 and 3
  refine Ends.callToThen (phase_step prog hw H inv₂ hd' ⟨0, 0, 0, 1, 3, -1, 1, 1, 3, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₃ ⟨inv₃, rest₃⟩
  -- M₄ = a₃ (b₂ - b₀) goes to 0 and 2
  refine Ends.callToThen (phase_step prog hw H inv₃ hd' ⟨3, 3, 0, 2, 0, -1, 0, 1, 2, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₄ ⟨inv₄, rest₄⟩
  -- M₅ = (a₀ + a₁) b₃ goes, with the sign -1, to 0, and to 1
  refine Ends.callToThen (phase_step prog hw H inv₄ hd' ⟨0, 1, 1, 3, 3, 0, 0, -1, 1, 1⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₅ ⟨inv₅, rest₅⟩
  -- M₆ = (a₂ - a₀) (b₀ + b₁) goes to 3
  refine Ends.callToThen (phase_step prog hw H inv₅ hd' ⟨2, 0, -1, 0, 1, 1, 3, 1, 0, 0⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₆ ⟨inv₆, rest₆⟩
  -- M₇ = (a₁ - a₃) (b₂ + b₃) goes to 0
  refine Ends.callTo (phase_step prog hw H inv₆ hd' ⟨1, 3, -1, 2, 3, 1, 0, 1, 3, 0⟩) ?_
    (hT := by simp; omega)
  rintro _ μ₇ ⟨inv₇, rest₇⟩
  -- The four lists are the four quadrants of the product.
  have hseg := seg_of_quarters (fun t ht => (inv₇.out t ht).seg) fun t ht => (inv₇.out t ht).len
  simp only [StrArgs.after, StrArgs.phase, Function.update_apply, Nat.reduceEqDiff, reduceIte,
    OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero, OfNat.one_ne_ofNat, OfNat.ofNat_ne_one, zero_ne_one,
    one_ne_zero] at hseg
  have key := strassenList_succ_eq_phases x.p j x.A x.B (inv.opA.len.trans inv.size)
    (inv.opB.len.trans inv.size)
  simp only [← inv.quarterLen] at key
  exact ⟨key ▸ hseg, by ((try refine Light.SameOn.cell ?_);
                              (intro apspMacro_173502_0 apspMacro_173502_1);
                              (first
                                |
                                  ((((repeat
                                            (((with_reducible
                                                    rename Light.SameOn _ _ _ => apspMacro_173502_2));
                                              ((try
                                                    have :=
                                                      apspMacro_173502_2 apspMacro_173502_0 (by omega)));
                                              (revert apspMacro_173502_2)));
                                        (intros);
                                        (try simp only [Function.update_apply, Light.wrote] at *)));
                                    (omega))
                                |
                                  ((simp [] at apspMacro_173502_1);
                                    (((repeat
                                            (((with_reducible
                                                    rename Light.SameOn _ _ _ => apspMacro_173502_3));
                                              ((try
                                                    have :=
                                                      apspMacro_173502_3 apspMacro_173502_0 (by omega)));
                                              (revert apspMacro_173502_3)));
                                        (intros);
                                        (try simp only [Function.update_apply, Light.wrote] at *)));
                                    (omega))
                                |
                                  ((((repeat
                                            (((with_reducible
                                                    rename Light.SameOn _ _ _ => apspMacro_173502_4));
                                              ((try
                                                    have :=
                                                      apspMacro_173502_4 apspMacro_173502_0 (by omega)));
                                              (revert apspMacro_173502_4)));
                                        (intros);
                                        (try simp only [Function.update_apply, Light.wrote] at *)));
                                    (fail
                                        "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                  SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                  its condition K x does not follow from the hypotheses."))))⟩

/-! ## The two cases and the induction -/

/-- **Level 0**: one product in the ring. -/
theorem strassen_zero : StrSpec lim P ν 0 := by
  intro x μ pre d hd
  have hq : x.len = x.p := by simpa using pre.size
  have hword : (x.p : ℤ) * (x.α * x.β) ≤ lim.word := by
    have h := pre.word
    have h0 : (0 : ℤ) ≤ x.p * (x.α * x.β) := by have := pre.oneA; have := pre.oneB; positivity
    rw [strassenBound, pow_zero, one_mul, mul_assoc] at h
    omega
  ((obtain ⟨⟩ := id pre); (obtain ⟨⟩ := id pre.opA); (obtain ⟨⟩ := id pre.opB))
  refine Meets.of_body prog.str ?_
  -- if j = 0 then cconv(dst, a, b, p)
  refine Ends.iteLast (fun _ => ?_) (fun hc => absurd (by simp) hc) (hT := by simp [strSteps])
  refine Ends.callTo (cconv_meets prog.cconv hw (dst := x.dst)
    { opA := (hq ▸ pre.opA).mono, opB := (hq ▸ pre.opB).mono, word := hword }) ?_
    (hT := by simp [strSteps]; omega)
  rintro _ μ' ⟨seg, rest⟩
  exact ⟨seg, by ((try refine Light.SameOn.cell ?_);
                     (intro apspMacro_174421_0 apspMacro_174421_1);
                     (first
                       |
                         ((((repeat
                                   (((with_reducible
                                           rename Light.SameOn _ _ _ => apspMacro_174421_2));
                                     ((try
                                           have :=
                                             apspMacro_174421_2 apspMacro_174421_0 (by omega)));
                                     (revert apspMacro_174421_2)));
                               (intros);
                               (try simp only [Function.update_apply, Light.wrote] at *)));
                           (omega))
                       |
                         ((simp [] at apspMacro_174421_1);
                           (((repeat
                                   (((with_reducible
                                           rename Light.SameOn _ _ _ => apspMacro_174421_3));
                                     ((try
                                           have :=
                                             apspMacro_174421_3 apspMacro_174421_0 (by omega)));
                                     (revert apspMacro_174421_3)));
                               (intros);
                               (try simp only [Function.update_apply, Light.wrote] at *)));
                           (omega))
                       |
                         ((((repeat
                                   (((with_reducible
                                           rename Light.SameOn _ _ _ => apspMacro_174421_4));
                                     ((try
                                           have :=
                                             apspMacro_174421_4 apspMacro_174421_0 (by omega)));
                                     (revert apspMacro_174421_4)));
                               (intros);
                               (try simp only [Function.update_apply, Light.wrote] at *)));
                           (fail
                               "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                         SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                         its condition K x does not follow from the hypotheses."))))⟩

/-- **Level j + 1**: clear the result, then the seven phases. -/
theorem strassen_succ (H : StrSpec lim P ν j) : StrSpec lim P ν (j + 1) := by
  intro x μ pre d hd
  obtain ⟨q, hq⟩ : ∃ q, q = 4 ^ j * x.p := ⟨_, rfl⟩
  have hsize : x.len = 4 * q := by rw [pre.size, hq]; ring
  ((obtain ⟨⟩ := id pre); (obtain ⟨⟩ := id pre.opA); (obtain ⟨⟩ := id pre.opB);
    (obtain ⟨⟩ := id pre.table))
  have hread : μ (x.szt + j) = q := by
    rw [pre.table.read (by omega), hq]
    simp [szList, show j < x.J + 1 by omega]
  refine Meets.of_body prog.str ?_
  rw [show strSteps x.p (j + 1) = 7 * strSteps x.p j + 696 * q + 900 by rw [strSteps, hq]]
  -- if level = 0 … else; the level is j + 1
  refine Ends.iteLast (fun hc => absurd hc (by simp; omega)) fun _ => ?_
  -- below := level - 1, which is j; q := szt[below]; q2 := q + q; q3 := q2 + q
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen j ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen q ?_ ?_ ?_);
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
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (2 * q : ℕ) ?_ ?_ ?_);
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
          (3 * q : ℕ)
            -- fill(dst, 4 q, 0)
            
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
  -- fill(dst, 4 q, 0)
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
            ((fill_meets prog.fill (dst := x.dst) (n := 4 * q) (x := 0) hw
                (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (fill_meets prog.fill (dst := x.dst) (n := 4 * q) (x := 0) hw
              (by omega))
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
        ((rintro r μ₁ ⟨segF, rest⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have inv : StrInv lim μ₁ j q x (fun _ => zeros q) 0 :=
    { toStrPre := pre.keep
      quarterLen := hq
      out := fun t ht =>
        { len := by simp [zeros], seg := seg_zeros_quarter segF ht
          bound := by simpa using absLe_zeros q
          below := by have := Nat.mul_add_le_mul ht (le_refl q); omega } }
  -- the seven phases
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen (sevenPhases_spec prog hw H inv (by omega) _ _ _)
            ?_ ?_
      |
        refine
          Light.Ends.pieceLast (sevenPhases_spec prog hw H inv (by omega) _ _ _)
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
    (on_goal -1 => rintro σ' ⟨seg, rest'⟩)
  exact ⟨seg, by ((try refine Light.SameOn.cell ?_);
                     (intro apspMacro_175910_0 apspMacro_175910_1);
                     (first
                       |
                         ((((repeat
                                   (((with_reducible
                                           rename Light.SameOn _ _ _ => apspMacro_175910_2));
                                     ((try
                                           have :=
                                             apspMacro_175910_2 apspMacro_175910_0 (by omega)));
                                     (revert apspMacro_175910_2)));
                               (intros);
                               (try simp only [Function.update_apply, Light.wrote] at *)));
                           (omega))
                       |
                         ((simp [] at apspMacro_175910_1);
                           (((repeat
                                   (((with_reducible
                                           rename Light.SameOn _ _ _ => apspMacro_175910_3));
                                     ((try
                                           have :=
                                             apspMacro_175910_3 apspMacro_175910_0 (by omega)));
                                     (revert apspMacro_175910_3)));
                               (intros);
                               (try simp only [Function.update_apply, Light.wrote] at *)));
                           (omega))
                       |
                         ((((repeat
                                   (((with_reducible
                                           rename Light.SameOn _ _ _ => apspMacro_175910_4));
                                     ((try
                                           have :=
                                             apspMacro_175910_4 apspMacro_175910_0 (by omega)));
                                     (revert apspMacro_175910_4)));
                               (intros);
                               (try simp only [Function.update_apply, Light.wrote] at *)));
                           (fail
                               "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                         SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                         its condition K x does not follow from the hypotheses."))))⟩

/-- **Strassen's algorithm**, at every level. -/
theorem strassen_spec : ∀ j, StrSpec lim P ν j
  | 0 => strassen_zero prog hw
  | j + 1 => strassen_succ prog hw (strassen_spec j)

end levels

end Light.Sec3

end
end

section


/-!
# The steps and the scratch space of Strassen's recursion

At level j the operands are 2^j × 2^j matrices whose entries are vectors of p numbers, so that an
operand has 4^j · p numbers.  strScr p j ≤ 4^j · p (`strScr_le`), and both strScr and strSteps are
monotone in p.
-/

public section

namespace Light.Sec3















/-- The scratch space grows with p. -/
theorem strScr_mono {p q : ℕ} (h : p ≤ q) (j : ℕ) : strScr p j ≤ strScr q j := by
  induction j with
  | zero => simp [strScr]
  | succ j ih =>
    rw [strScr, strScr]
    have := Nat.mul_le_mul_left (4 ^ j) h
    omega

/-- The number of steps grows with p. -/
theorem strSteps_mono {p q : ℕ} (h : p ≤ q) (j : ℕ) : strSteps p j ≤ strSteps q j := by
  induction j with
  | zero =>
    rw [strSteps, strSteps]
    have h2 : p * p ≤ q * q := Nat.mul_le_mul h h
    have e1 : 32 * p * p = 32 * (p * p) := by ring
    have e2 : 32 * q * q = 32 * (q * q) := by ring
    omega
  | succ j ih =>
    rw [strSteps, strSteps]
    have := Nat.mul_le_mul_left (4 ^ j) h
    omega

end Light.Sec3

end
end

section


/-!
# Matrices over ℤ[x]/(x^p - 1) in Z-order: the table of places, and P and Q of Theorem 17's proof

spreadTable(dst, N2) writes the table of `spread`: the number with the binary digits of i, read in
base 4.  There is no division: a pointer j = ⌊i/2⌋ and the parity of i are carried along, and
dst[i] = 4 dst[j] + parity (`spreadStep_spec`, `spreadTable_spec`).

buildZ(dst, r, mort, n, N2, p, mx, my), with N2 = 2^K, writes an N2 × N2 matrix of vectors of length
p in Z-order, 4^K p cells in all, whose entry for the pair (x, y), x, y < n, is the unit vector with
its 1 at place r[x n + y], and whose other entries are zero vectors.  Here mort is the address of
the table that spreadTable has written, so that mort[x] = spread x.  The place of the pair (x, y) is
mx · spread x + my · spread y.  With (mx, my) = (2, 1) the pair is (row, column), which gives
"P[a,c] := x^{w(a,c) mod p}"; with (1, 2) it is (column, row), which gives
"Q[c,b] := x^{w(b,c) mod p}" from the residues of w(b,c) stored at b n + c.  (Inside the two quoted
formulas x is the paper's indeterminate, and P and Q are the paper's matrices; in the code `P` is
the program.)  The routine clears the matrix (`buildZClear_spec`) and marks one cell for each pair
(`buildZMark_spec`); `markList_eq_zList` identifies the marked list with the matrix.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The table of places -/

namespace SpreadTable









end SpreadTable



















section spreadTable

variable {μ μ' : ℕ → ℤ} {dst N₂ : ℕ}

open SpreadTable in
/-- **One entry of the table.** -/
theorem spreadStep_spec (hw : (lim.space : ℤ) ≤ lim.word) (h4 : (4 : ℤ) ≤ lim.word)
    (hsq : ((N₂ * N₂ : ℕ) : ℤ) ≤ lim.word) (hdst : dst + N₂ ≤ lim.space) {i : ℕ} (hi0 : 0 < i)
    (hi : i < N₂) (hseg : Seg μ' dst (spreadList i)) :
    Ends lim P d spreadStep ⟨frame [dst, N₂, i, (i / 2 : ℕ), (i % 2 : ℕ)], μ'⟩ 26 fun σ' =>
      σ' = ⟨frame [dst, N₂, (i + 1 : ℕ), ((i + 1) / 2 : ℕ), ((i + 1) % 2 : ℕ)],
        Function.update μ' (dst + i) (spread i : ℕ)⟩ := by
  have hcell : μ' (dst + i / 2) = (spread (i / 2) : ℕ) := seg_spreadList_get hseg (by omega)
  have hspread := spread_eq i
  have hle : spread i ≤ N₂ * N₂ := (spread_le_sq i).trans (Nat.mul_le_mul hi.le hi.le)
  have heven : i % 2 = 0 → (i + 1) / 2 = i / 2 ∧ (i + 1) % 2 = 1 := by omega
  have hodd : i % 2 ≠ 0 → (i + 1) / 2 = i / 2 + 1 ∧ (i + 1) % 2 = 0 := by omega
  have hj : i / 2 < i := by omega
  have hb : i % 2 < 2 := by omega
  generalize i / 2 = j at *
  generalize i % 2 = b at *
  -- dst[i] := 4 dst[j] + parity
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen (dst + i) (spread i : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcell]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcell] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcell] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- if parity = 0 then parity := 1 else parity := 0; j := j + 1
  -- i := i + 1
  refine Ends.iteThen (fun h0 => ?_) (fun h0 => ?_)
  · have h0 : b = 0 := by simpa using h0
    rw [(heven h0).1, (heven h0).2]
    exact Ends.setToThen (1 : ℕ) (Ends.setTo (i + 1 : ℕ) rfl)
  · have h0 : b ≠ 0 := by simpa using h0
    rw [(hodd h0).1, (hodd h0).2]
    exact Ends.seqAssoc
      (Ends.setToThen (0 : ℕ) (Ends.setToThen (j + 1 : ℕ) (Ends.setTo (i + 1 : ℕ) rfl)))

open SpreadTable in
/-- **spreadTable**: at most 30 N2 + 17 steps. -/
theorem spreadTable_spec (hw : (lim.space : ℤ) ≤ lim.word) (h4 : (4 : ℤ) ≤ lim.word)
    (hsq : ((N₂ * N₂ : ℕ) : ℤ) ≤ lim.word) (hdst : dst + N₂ ≤ lim.space) :
    Ends lim P d spreadTableBody ⟨frame [dst, N₂], μ⟩ (30 * N₂ + 17) fun σ' =>
      Seg σ'.mem dst (spreadList N₂) ∧ SameOutside μ σ'.mem dst N₂ := by
  -- if 0 < N2
  refine Ends.iteLast (fun hpos => ?_) (fun hzero => ?_)
  swap
  · obtain rfl : N₂ = 0 := by simpa using hzero
    exact Ends.skip ⟨by simp [spreadList], .refl⟩
  have hN : 0 < N₂ := by simpa using hpos
  -- dst[0] := 0; i := 1; j := 0; parity := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen dst 0 ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
          (1 : ℕ)
            -- while i < N2; before round r the counter is r + 1
            
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
  -- while i < N2; before round r the counter is r + 1
  refine Ends.whileConst (fun r σ => ∃ μ' : ℕ → ℤ,
      σ = ⟨frame [dst, N₂, (r + 1 : ℕ), ((r + 1) / 2 : ℕ), ((r + 1) % 2 : ℕ)], μ'⟩ ∧
      Seg μ' dst (spreadList (r + 1)) ∧ SameOutside μ μ' dst N₂) (N₂ - 1) 26
    ?start ?round ?done (by first
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
  case start =>
    refine ⟨_, rfl, fun i hi => ?_, SameOutside.refl.update ⟨le_rfl, by omega⟩ _⟩
    obtain rfl : i = 0 := by simpa [spreadList] using hi
    simp [spreadList, spread_zero]
  case done =>
    rintro _ ⟨μ', rfl, hseg, hrest⟩
    rw [show N₂ - 1 + 1 = N₂ by omega] at hseg ⊢
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hseg, hrest⟩
  case round =>
    rintro r _ hr ⟨μ', rfl, hseg, hrest⟩
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      (spreadStep_spec hw h4 hsq hdst (Nat.succ_pos r) (by omega) hseg).mono le_rfl ?_⟩
    rintro _ rfl
    refine ⟨_, rfl, ?_, hrest.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := hseg.snoc (spread (r + 1) : ℕ)
    rw [length_spreadList] at hsnoc
    rwa [spreadList_succ]

end spreadTable

/-- **spreadTable** as a procedure. -/
theorem spreadTable_meets {μ : ℕ → ℤ} {q dst N2 : ℕ} (hP : P[q]? = some spreadTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (h4 : (4 : ℤ) ≤ lim.word)
    (hsq : ((N2 * N2 : ℕ) : ℤ) ≤ lim.word) (hdst : dst + N2 ≤ lim.space) :
    Meets lim P q d [dst, N2] μ (30 * N2 + 17) fun _ μ' =>
      Seg μ' dst (spreadList N2) ∧ SameOutside μ μ' dst N2 :=
  Meets.of_body hP (spreadTable_spec hw h4 hsq hdst)

/-! ## The matrices -/

namespace BuildZ




















end BuildZ








































/-! ### The pure side: a list of zeros in which places are marked one after the other -/






theorem length_markList (len : ℕ) (idx : ℕ → ℕ) (t : ℕ) : (markList len idx t).length = len := by
  induction t with
  | zero => simp [markList]
  | succ t ih => simp [markList, ih]

open Classical in
/-- An entry of the list is 1 if its place has been marked, and 0 if not. -/
theorem getD_markList {len : ℕ} (idx : ℕ → ℕ) (t : ℕ) {i : ℕ} (hi : i < len) :
    (markList len idx t).getD i 0 = if ∃ s < t, idx s = i then 1 else 0 := by
  induction t with
  | zero => simp [markList, List.getD_eq_getElem?_getD, hi]
  | succ t ih =>
    rw [markList, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases h : idx t = i
    · rw [if_pos h, if_pos (by rw [length_markList, h]; exact hi), if_pos
        ⟨t, Nat.lt_succ_self t, h⟩]
      rfl
    · rw [if_neg h, ← List.getD_eq_getElem?_getD, ih]
      refine if_congr ⟨fun ⟨s, hs, e⟩ => ⟨s, by omega, e⟩, fun ⟨s, hs, e⟩ => ⟨s, ?_, e⟩⟩ rfl rfl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with h' | h'
      · exact h'
      · exact absurd (h' ▸ e) h

theorem getD_vunit {p k s : ℕ} (hs : s < p) : (vunit p k).getD s 0 = if s = k then 1 else 0 := by
  rw [vunit, List.getD_eq_getElem _ _ (by simpa using hs)]
  simp

theorem getD_zeros (p s : ℕ) : (zeros p).getD s 0 = 0 := by
  rw [zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

/-- A unit vector and the zero vector have p entries. -/
theorem length_unitOrZero (c : Prop) [Decidable c] (p k : ℕ) :
    (if c then vunit p k else zeros p).length = p := by
  split_ifs <;> simp [vunit, zeros]

/-- **A matrix of unit vectors, by marking.**  The pairs are numbered by `t < m`; pair number `t`
stands in row `ρ t` and column `κ t`, and `τ` gives the number of the pair in a row and a column. -/
theorem markList_eq_zList {n K p m : ℕ} (R : List ℕ) (ρ κ : ℕ → ℕ) (τ : ℕ → ℕ → ℕ)
    (hR : ∀ t < m, R.getD t 0 < p) (hcoords : ∀ t < m, ρ t < n ∧ κ t < n ∧ τ (ρ t) (κ t) = t)
    (hnumber : ∀ a < n, ∀ c < n, τ a c < m ∧ ρ (τ a c) = a ∧ κ (τ a c) = c) :
    markList (4 ^ K * p) (fun t => zIdx (ρ t) (κ t) * p + R.getD t 0) m
      = zList K fun a c => if a < n ∧ c < n then vunit p (R.getD (τ a c) 0) else zeros p := by
  have hlenM : ∀ a c,
      (if a < n ∧ c < n then vunit p (R.getD (τ a c) 0) else zeros p).length = p :=
    fun _ _ => length_unitOrZero _ _ _
  refine List.ext_getElem (by rw [length_markList, length_zList _ _ hlenM]) fun i hi₁ hi₂ => ?_
  have hi : i < 4 ^ K * p := by rwa [length_markList] at hi₁
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h] at hi; omega
    · exact h
  rw [← List.getD_eq_getElem _ 0 hi₁, ← List.getD_eq_getElem _ 0 hi₂, getD_markList _ _ hi]
  have hz : i / p < 4 ^ K := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
  have hs : i % p < p := Nat.mod_lt _ hp
  have hsplit : i = i / p * p + i % p := (Nat.div_add_mod' i p).symm
  have hget :
      (zList K fun a c => if a < n ∧ c < n then vunit p (R.getD (τ a c) 0) else zeros p).getD i 0 =
        (if zRow (i / p) < n ∧ zCol (i / p) < n then
          vunit p (R.getD (τ (zRow (i / p)) (zCol (i / p))) 0) else zeros p).getD (i % p) 0 := by
    conv_lhs => rw [hsplit]
    exact List.getD_flatMap_range _ (fun _ _ => hlenM _ _) hz hs 0
  rw [hget]
  have hplace : ∀ t < m, zIdx (ρ t) (κ t) * p + R.getD t 0 = i → zIdx (ρ t) (κ t) = i / p :=
    fun t ht e => by
      rw [← e, Nat.mul_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt (hR t ht), Nat.add_zero]
  by_cases hac : zRow (i / p) < n ∧ zCol (i / p) < n
  · obtain ⟨g1, g2, g3⟩ := hnumber _ hac.1 _ hac.2
    rw [if_pos hac, getD_vunit hs]
    refine if_congr ⟨?_, fun e => ⟨_, g1, ?_⟩⟩ rfl rfl
    · rintro ⟨t, ht, e⟩
      have hRt := hR t ht
      have e1 := hplace t ht e
      have e2 : R.getD t 0 = i % p := by
        rw [← e, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hRt]
      rw [← e1, zRow_zIdx, zCol_zIdx, (hcoords t ht).2.2, e2]
    · rw [g2, g3, zIdx_zRow_zCol, ← e]
      exact hsplit.symm
  · rw [if_neg hac, getD_zeros, if_neg]
    rintro ⟨t, ht, e⟩
    have e1 := hplace t ht e
    exact hac ⟨by rw [← e1, zRow_zIdx]; exact (hcoords t ht).1,
      by rw [← e1, zCol_zIdx]; exact (hcoords t ht).2.1⟩

/-- The first matrix of the proof of Theorem 17, P, by marking. -/
theorem markList_eq_matPList {n K p : ℕ} (R : List ℕ) (hR : ∀ t < n * n, R.getD t 0 < p) :
    markList (4 ^ K * p) (fun t => (2 * spread (t / n) + 1 * spread (t % n)) * p + R.getD t 0)
      (n * n) = matPList n p K R := by
  have h := markList_eq_zList (K := K) (m := n * n) R (fun t => t / n) (fun t => t % n)
    (fun a c => a * n + c) hR
    (fun t ht => ⟨Nat.div_lt_of_lt_mul' ht, Nat.mod_lt_of_lt_mul ht, Nat.div_add_mod' _ _⟩)
      fun a ha c hc =>
      ⟨Nat.mul_add_lt_mul ha hc, Nat.mul_add_div_of_lt hc, Nat.mul_add_mod_of_lt hc⟩
  simpa only [zIdx, Nat.one_mul, matPList] using h

/-- The second matrix of the proof of Theorem 17, Q, by marking. -/
theorem markList_eq_matQList {n K p : ℕ} (R : List ℕ) (hR : ∀ t < n * n, R.getD t 0 < p) :
    markList (4 ^ K * p) (fun t => (1 * spread (t / n) + 2 * spread (t % n)) * p + R.getD t 0)
      (n * n) = matQList n p K R := by
  have h := markList_eq_zList (K := K) (m := n * n) R (fun t => t % n) (fun t => t / n)
    (fun c b => b * n + c) hR
    (fun t ht => ⟨Nat.mod_lt_of_lt_mul ht, Nat.div_lt_of_lt_mul' ht, Nat.div_add_mod' _ _⟩)
    fun c hc b hb => ⟨Nat.mul_add_lt_mul hb hc, Nat.mul_add_mod_of_lt hc, Nat.mul_add_div_of_lt hc⟩
  simpa only [zIdx, Nat.one_mul, Nat.add_comm (spread (_ / n)), matQList] using h

/-! ### The program -/

section buildZ

variable {μ μ' : ℕ → ℤ} {dst r mort n K p mx my : ℕ} {R : List ℕ}

namespace BuildZPre

/-- The residues lie outside the matrix, so they can be read at any time. -/
theorem readR (pre : BuildZPre lim μ dst r mort n K p R) (h : SameOutside μ μ' dst (4 ^ K * p))
    {t : ℕ} (ht : t < n * n) : μ' (r + t) = (R.getD t 0 : ℕ) := by
  (obtain ⟨⟩ := id pre)
  exact pre.res.keep.read ht

/-- The table of places lies outside the matrix, so it can be read at any time. -/
theorem readM (pre : BuildZPre lim μ dst r mort n K p R) (h : SameOutside μ μ' dst (4 ^ K * p))
    {x : ℕ} (hx : x < n) : μ' (mort + x) = (spread x : ℕ) := by
  (obtain ⟨⟩ := id pre)
  exact seg_spreadList_get pre.table.keep.seg (by omega)

end BuildZPre

open BuildZ in
/-- **The matrix is cleared.** -/
theorem buildZClear_spec (hw : (lim.space : ℤ) ≤ lim.word) {N₂ len : ℕ}
    (hlen : N₂ * N₂ * p = len) (hsq : N₂ * N₂ ≤ len) (hspace : dst + len < lim.space) :
    Ends lim P d buildZClear ⟨frame [dst, r, mort, n, N₂, p, mx, my], μ⟩ (11 * len + 14) fun σ' =>
      ∃ μ' : ℕ → ℤ,
        σ' = ⟨frame [dst, r, mort, n, N₂, p, mx, my, (dst + len : ℕ), (dst + len : ℕ)], μ'⟩ ∧
        Seg μ' dst (List.replicate len 0) ∧ SameOutside μ μ' dst len := by
  have hlenZ : (N₂ : ℤ) * N₂ * p = len := by exact_mod_cast hlen
  -- ptr := dst; end := dst + N2 N2 p
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_);
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
          (dst + len : ℕ)
            -- while ptr < end
            
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
  -- while ptr < end
  refine Ends.whileConst (fun i σ => ∃ μ' : ℕ → ℤ,
      σ = ⟨frame [dst, r, mort, n, N₂, p, mx, my, (dst + i : ℕ), (dst + len : ℕ)], μ'⟩ ∧
      Seg μ' dst (List.replicate i 0) ∧ SameOutside μ μ' dst len) len 7
    ⟨μ, rfl, by simp, .refl⟩ ?round ?done (by first
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
  case done =>
    rintro _ ⟨μ', rfl, hseg, hrest⟩
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), μ', rfl, hseg, hrest⟩
  case round =>
    rintro i _ hi ⟨μ', rfl, hseg, hrest⟩
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- mem[ptr] := 0; ptr := ptr + 1
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (dst + i) 0 ?_ ?_ ?_);
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
      (refine Light.Ends.setToThen (dst + (i + 1) : ℕ) ?_ ?_ ?_);
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
    refine ⟨_, rfl, ?_, hrest.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := hseg.snoc 0
    rw [List.length_replicate] at hsnoc
    rwa [List.replicate_succ']

open BuildZ in
/-- **The pair number t marks its cell.** -/
theorem buildZMark_spec (pre : BuildZPre lim μ dst r mort n K p R)
    (hplace : ∀ x < n, ∀ y < n, mx * spread x + my * spread y < 4 ^ K) {t : ℕ} (ht : t < n * n)
    (ptr e : ℤ) (hrest : SameOutside μ μ' dst (4 ^ K * p)) :
    Ends lim P d buildZMark
      ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, mx, my, ptr, e, (n * n : ℕ), t, (t / n : ℕ),
        (t % n : ℕ)], μ'⟩ 24 fun σ' =>
      σ' = ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, mx, my, ptr, e, (n * n : ℕ), t, (t / n : ℕ),
        (t % n : ℕ)], Function.update μ'
          (dst + ((mx * spread (t / n) + my * spread (t % n)) * p + R.getD t 0)) 1⟩ := by
  ((obtain ⟨⟩ := id pre); (obtain ⟨⟩ := id pre.res); (obtain ⟨⟩ := id pre.table))
  have hrow : t / n < n := Nat.div_lt_of_lt_mul' ht
  have hcol : t % n < n := Nat.mod_lt_of_lt_mul ht
  have hreadX := pre.readM hrest hrow
  have hreadY := pre.readM hrest hcol
  have hreadR := pre.readR hrest ht
  have hidx := Nat.mul_add_lt_mul (hplace _ hrow _ hcol) (pre.res.getD_lt ht)
  have hz := hplace _ hrow _ hcol
  have h4 : 4 ^ K ≤ 4 ^ K * p := Nat.le_mul_of_pos_right _ pre.p_pos
  generalize R.getD t 0 = rho at *
  generalize t / n = x at *
  generalize t % n = y at *
  generalize spread x = sx at *
  generalize spread y = sy at *
  have hidxZ : ((mx : ℤ) * sx + my * sy) * p + rho < (4 ^ K * p : ℕ) := by exact_mod_cast hidx
  have hzZ : (mx : ℤ) * sx + my * sy < (4 ^ K : ℕ) := by exact_mod_cast hz
  have hx0 : (0 : ℤ) ≤ (mx : ℤ) * sx := by positivity
  have hy0 : (0 : ℤ) ≤ (my : ℤ) * sy := by positivity
  have hp0 : (0 : ℤ) ≤ ((mx : ℤ) * sx + my * sy) * p := by positivity
  exact Ends.storeTo (dst + ((mx * sx + my * sy) * p + rho)) 1 rfl
    (by (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadX, hreadY, hreadR] <;>
              omega)))

open BuildZ in
/-- **buildZ**, for any two multipliers that keep the places inside the matrix. -/
theorem buildZ_spec (pre : BuildZPre lim μ dst r mort n K p R)
    (hplace : ∀ x < n, ∀ y < n, mx * spread x + my * spread y < 4 ^ K) :
    Ends lim P d buildZBody ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, mx, my], μ⟩
      (buildZTime n (2 ^ K) p) fun σ' =>
      Seg σ'.mem dst (markList (4 ^ K * p)
        (fun t => (mx * spread (t / n) + my * spread (t % n)) * p + R.getD t 0) (n * n)) ∧
        SameOutside μ σ'.mem dst (4 ^ K * p) := by
  ((obtain ⟨⟩ := id pre); (obtain ⟨⟩ := id pre.res); (obtain ⟨⟩ := id pre.table))
  have h44 : 2 ^ K * 2 ^ K = 4 ^ K := by rw [← mul_pow]; norm_num
  have h4 : 4 ^ K ≤ 4 ^ K * p := Nat.le_mul_of_pos_right _ pre.p_pos
  have h44p : 2 ^ K * 2 ^ K * p = 4 ^ K * p := by rw [h44]
  unfold buildZTime
  rw [h44]
  -- the matrix is cleared
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen
            (buildZClear_spec pre.space_le h44p (by omega) pre.dst_le) ?_ ?_
      |
        refine
          Light.Ends.pieceLast
            (buildZClear_spec pre.space_le h44p (by omega) pre.dst_le) ?_ ?_);
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
        rintro _
          ⟨μ₁, rfl, hzero, hrest⟩
              -- nn := n n; x := 0; y := 0
              )
  -- nn := n n; x := 0; y := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (n * n : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
          (0 : ℕ)
            -- for t < nn
            
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
  -- for t < nn
  refine Ends.for (fun t σ => ∃ μ' : ℕ → ℤ,
      σ = ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, mx, my, (dst + 4 ^ K * p : ℕ),
        (dst + 4 ^ K * p : ℕ), (n * n : ℕ), t, (t / n : ℕ), (t % n : ℕ)], μ'⟩ ∧
      Seg μ' dst (markList (4 ^ K * p)
        (fun t => (mx * spread (t / n) + my * spread (t % n)) * p + R.getD t 0) t) ∧
      SameOutside μ μ' dst (4 ^ K * p)) (n * n) 38 ?start ?round ?done ?bound
  case start =>
    refine ⟨μ₁, ?_, hzero, hrest⟩
    rw [update_frame_setLocal, Nat.zero_div, Nat.zero_mod]
    rfl
  case bound =>
    rintro t _ - - ⟨μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨μ', rfl, hseg, hr⟩
    exact ⟨hseg, hr⟩
  case round =>
    rintro t _ ht - ⟨μ', rfl, hseg, hr⟩
    have hn : 0 < n := Nat.pos_of_ne_zero fun e => by simp [e] at ht
    have hidx :=
      Nat.mul_add_lt_mul (hplace _ (Nat.div_lt_of_lt_mul' ht) _ (Nat.mod_lt_of_lt_mul ht))
      (pre.res.getD_lt ht)
    refine Ends.next 24 ((buildZMark_spec pre hplace ht _ _ hr).mono le_rfl ?_)
    rintro _ rfl
    refine Ends.nextPair ?_ hn (by omega) (by omega) rfl rfl rfl
    exact ⟨by simp, _, by rw [update_frame_setLocal]; rfl,
      hseg.update_in (by rw [length_markList]; exact hidx) 1,
      hr.update ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hidx _⟩ _⟩

/-- **buildZ with (mx, my) = (2, 1)**: the matrix P of the proof of Theorem 17 (not the program
`P`). -/
theorem buildZ_P_spec (pre : BuildZPre lim μ dst r mort n K p R) :
    Ends lim P d buildZBody ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, 2, 1], μ⟩
      (buildZTime n (2 ^ K) p) fun σ' =>
      Seg σ'.mem dst (matPList n p K R) ∧ SameOutside μ σ'.mem dst (4 ^ K * p) := by
  have h := buildZ_spec (P := P) (d := d) (mx := 2) (my := 1) pre fun x hx y hy => by
    have := zIdx_lt (K := K) (lt_of_lt_of_le hx pre.n_le) (lt_of_lt_of_le hy pre.n_le)
    simpa [zIdx] using this
  rwa [markList_eq_matPList R fun t ht => pre.res.getD_lt ht] at h

/-- **buildZ with (mx, my) = (1, 2)**: the matrix Q of the proof of Theorem 17. -/
theorem buildZ_Q_spec (pre : BuildZPre lim μ dst r mort n K p R) :
    Ends lim P d buildZBody ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, 1, 2], μ⟩
      (buildZTime n (2 ^ K) p) fun σ' =>
      Seg σ'.mem dst (matQList n p K R) ∧ SameOutside μ σ'.mem dst (4 ^ K * p) := by
  have h := buildZ_spec (P := P) (d := d) (mx := 1) (my := 2) pre fun x hx y hy => by
    have := zIdx_lt (K := K) (lt_of_lt_of_le hy pre.n_le) (lt_of_lt_of_le hx pre.n_le)
    simp only [zIdx] at this
    omega
  rwa [markList_eq_matQList R fun t ht => pre.res.getD_lt ht] at h

end buildZ

/-- **buildZ** as a procedure, for the matrix P. -/
theorem buildZ_P_meets {μ : ℕ → ℤ} {q dst r mort n K p : ℕ} {R : List ℕ}
    (hP : P[q]? = some buildZBody) (pre : BuildZPre lim μ dst r mort n K p R) :
    Meets lim P q d [dst, r, mort, n, (2 ^ K : ℕ), p, 2, 1] μ (buildZTime n (2 ^ K) p) fun _ μ' =>
      Seg μ' dst (matPList n p K R) ∧ SameOutside μ μ' dst (4 ^ K * p) :=
  Meets.of_body hP (buildZ_P_spec pre)

/-- **buildZ** as a procedure, for the matrix Q. -/
theorem buildZ_Q_meets {μ : ℕ → ℤ} {q dst r mort n K p : ℕ} {R : List ℕ}
    (hP : P[q]? = some buildZBody) (pre : BuildZPre lim μ dst r mort n K p R) :
    Meets lim P q d [dst, r, mort, n, (2 ^ K : ℕ), p, 1, 2] μ (buildZTime n (2 ^ K) p) fun _ μ' =>
      Seg μ' dst (matQList n p K R) ∧ SameOutside μ μ' dst (4 ^ K * p) :=
  Meets.of_body hP (buildZ_Q_spec pre)

/-! ## The matrices P and Q as lists -/

/-- The matrix P has 4^K vectors of p numbers. -/
theorem length_matPList (n p K : ℕ) (R : List ℕ) : (matPList n p K R).length = 4 ^ K * p :=
  length_zList _ _ fun _ _ => length_unitOrZero _ _ _

/-- The matrix Q has 4^K vectors of p numbers. -/
theorem length_matQList (n p K : ℕ) (R : List ℕ) : (matQList n p K R).length = 4 ^ K * p :=
  length_zList _ _ fun _ _ => length_unitOrZero _ _ _

/-- The entries of a unit vector and of the zero vector are 0 or 1. -/
theorem absLe_unitOrZero (c : Prop) [Decidable c] (p k : ℕ) :
    AbsLe (if c then vunit p k else zeros p) 1 := by
  intro x hx
  split_ifs at hx
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    split_ifs <;> simp
  · rw [zeros, List.mem_replicate] at hx
    simp [hx.2]

/-- The entries of a matrix of unit vectors and zero vectors are 0 or 1. -/
theorem absLe_zList_unit (K : ℕ) (M : ℕ → ℕ → List ℤ) (hM : ∀ a c, AbsLe (M a c) 1) :
    AbsLe (zList K M) 1 := by
  intro x hx
  obtain ⟨z, -, hz⟩ := List.mem_flatMap.1 hx
  exact hM _ _ x hz

/-- The entries of P are 0 or 1. -/
theorem absLe_matPList (n p K : ℕ) (R : List ℕ) : AbsLe (matPList n p K R) 1 :=
  absLe_zList_unit _ _ fun _ _ => absLe_unitOrZero _ _ _

/-- The entries of Q are 0 or 1. -/
theorem absLe_matQList (n p K : ℕ) (R : List ℕ) : AbsLe (matQList n p K R) 1 :=
  absLe_zList_unit _ _ fun _ _ => absLe_unitOrZero _ _ _

end Light.Sec3

end
end

section


/-!
# Residues without division

"We reduce the weights modulo a prime p" (proof of Theorem 17).  The language has no division.  The
residue of a number w modulo p is found by greedy subtraction of 2^len p, …, 2p, p, which are kept
in a table.

* bitLen(U) returns the number of binary digits of U, by doubling (`bitLen_spec`).
* dblTable(dst, p, len) writes p, 2p, …, 2^len p to dst (`dblTable_spec`).
* resid(w, dbl, len) returns w mod p, for |w| < 2^len, given the table at dbl (`resid_meets`).  What
  the routine holds after i rounds is `greedyAt p len w i`: it is not negative, below 2^(len+1-i) p,
  and congruent to w (`greedyAt_inv`), so that it ends with the residue (`greedyAt_end`).
* residues(src, dst, m, dbl, len) writes the residues of the m numbers at src to dst, by one call of
  resid for each (`residues_spec`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The number of binary digits -/

namespace BitLen






end BitLen














/-- **bitLen** returns the least len with U < 2^len and changes no cell.  It forms numbers up to
2U + 1. -/
theorem bitLen_spec {μ : ℕ → ℤ} {U : ℕ} (hU : ((2 * U + 2 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d bitLenBody ⟨frame [U], μ⟩ (tBitLen U) fun σ' =>
      σ'.loc 0 = (bitLen U : ℕ) ∧ σ'.mem = μ := by
  have hlow : ∀ j, j < bitLen U → 2 ^ j ≤ U := fun j hj => Nat.lt_size.1 hj
  have hup : U < 2 ^ bitLen U := Nat.lt_size_self U
  push_cast at hU
  unfold tBitLen
  generalize bitLen U = n at hlow hup
  -- len := 0; pow := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
          (1 : ℕ)
            -- while pow ≤ U: pow := pow + pow; len := len + 1.  Before round j, len = j and pow = 2^j.
            
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
  -- while pow ≤ U: pow := pow + pow; len := len + 1.  Before round j, len = j and pow = 2^j.
  refine Ends.next _ (Ends.whileBlock (fun j σ => σ = ⟨frame [U, j, (2 ^ j : ℕ)], μ⟩) n
    (by simp) ?round ?done le_rfl)
  case round =>
    rintro j _ hj rfl
    have hpow := hlow j hj
    have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
    have hsucc : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by ring
    rw [hsucc]
    generalize 2 ^ j = q at hpow hjlt
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hupZ : (U : ℤ) < 2 ^ n := by exact_mod_cast hup
    -- return len
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), Ends.setTo n (by simp)⟩

/-! ## The table of the doubles -/

/-- One more entry of the table. -/
theorem dblList_succ (p len : ℕ) :
    dblList p (len + 1) = dblList p len ++ [((p * 2 ^ (len + 1) : ℕ) : ℤ)] := by
  simp [dblList, List.range_succ]

/-- The table has len + 1 entries. -/
@[simp] theorem length_dblList (p len : ℕ) : (dblList p len).length = len + 1 := by simp [dblList]

/-- Entry j of the table is 2^j p. -/
theorem read_dblList {μ : ℕ → ℤ} {dbl p len j : ℕ} (h : Seg μ dbl (dblList p len)) (hj : j ≤ len) :
    μ (dbl + j) = ((p * 2 ^ j : ℕ) : ℤ) := by
  rw [h j (by simp; omega)]
  simp [dblList]

namespace DblTable








end DblTable





















/-- **dblTable** writes p, 2p, …, 2^len p and changes nothing else.  It forms numbers up to
2^len p. -/
theorem dblTable_spec {μ : ℕ → ℤ} {dst p len : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst + (len + 1) ≤ lim.space) (hp : ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d dblTableBody ⟨frame [dst, p, len], μ⟩ (tDblTable len) fun σ' =>
      Seg σ'.mem dst (dblList p len) ∧ SameOutside μ σ'.mem dst (len + 1) := by
  have hfits : ∀ j ≤ len, ((p * 2 ^ j : ℕ) : ℤ) ≤ lim.word := fun j hj =>
    le_trans (by exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) hj)) hp
  unfold tDblTable
  -- exp := 0; entry := p; dst[0] := entry
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen p ?_ ?_ ?_);
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
    (refine Light.Ends.storeToThen dst p ?_ ?_ ?_);
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
  -- while exp < len
  refine Ends.whileBlock (DblInv μ dst p len) len ?start ?round ?done
  case start =>
    refine ⟨Function.update μ dst p, by simp, ?_, SameOutside.refl.update ⟨by omega, by omega⟩ _⟩
    simpa [dblList] using (Seg.nil (μ := μ) (a := dst)).snoc p
  case round =>
    rintro j _ hj ⟨μ', rfl, seg, rest⟩
    have hnext := hfits (j + 1) hj
    have hdouble : p * 2 ^ (j + 1) = p * 2 ^ j + p * 2 ^ j := by ring
    have haddr : ((dst : ℤ) + ((j : ℤ) + 1)).toNat = dst + (dblList p j).length := by
      rw [length_dblList]
      omega
    -- entry := entry + entry; exp := exp + 1; dst[exp] := entry
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_, Function.update μ' (dst + (dblList p j).length)
      ((p * 2 ^ (j + 1) : ℕ) : ℤ), ?_, dblList_succ p j ▸ seg.snoc _,
      rest.update ⟨by omega, by rw [length_dblList]; omega⟩ _⟩
    · rw [hdouble] at hnext
      generalize p * 2 ^ j = q at hnext
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))
    · rw [hdouble]
      simp [update_frame_setLocal, haddr]
  case done =>
    rintro _ ⟨μ', rfl, seg, rest⟩
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), seg, rest⟩

/-! ## One residue -/










/-- A multiple of p is congruent to 0. -/
private theorem mul_pow_modEq_zero (p j : ℕ) : ((p * 2 ^ j : ℕ) : ℤ) ≡ 0 [ZMOD (p : ℤ)] := by
  rw [Int.modEq_zero_iff_dvd, Nat.cast_mul]
  exact Dvd.intro _ rfl

/-- 2^(j+1) p is twice 2^j p. -/
private theorem cast_mul_pow_succ (p j : ℕ) :
    ((p * 2 ^ (j + 1) : ℕ) : ℤ) = 2 * ((p * 2 ^ j : ℕ) : ℤ) := by
  rw [pow_succ]
  push_cast
  ring

/-- After i rounds the number is not negative, below 2^(len+1-i) p, and congruent to w. -/
theorem greedyAt_inv {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) : ∀ i, i ≤ len + 1 →
    0 ≤ greedyAt p len w i ∧ greedyAt p len w i < ((p * 2 ^ (len + 1 - i) : ℕ) : ℤ) ∧
      greedyAt p len w i ≡ w [ZMOD (p : ℤ)] := by
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨hlow, hhigh⟩ := abs_lt.1 hw
    have hle : (2 : ℤ) ^ len ≤ ((p * 2 ^ len : ℕ) : ℤ) := by
      exact_mod_cast Nat.le_mul_of_pos_left (2 ^ len) hp
    rw [greedyAt, Nat.sub_zero, cast_mul_pow_succ]
    exact ⟨by linarith, by linarith,
      by simpa only [add_zero] using (Int.ModEq.refl w).add (mul_pow_modEq_zero p len)⟩
  | succ i ih =>
    intro hi
    obtain ⟨hlow, hhigh, hmod⟩ := ih (by omega)
    rw [show len + 1 - i = (len - i) + 1 by omega, cast_mul_pow_succ] at hhigh
    rw [show len + 1 - (i + 1) = len - i by omega, greedyAt]
    split_ifs with h
    · exact ⟨by linarith, by linarith,
        by simpa only [sub_zero] using hmod.sub (mul_pow_modEq_zero p (len - i))⟩
    · exact ⟨hlow, by linarith, hmod⟩

/-- Greedy subtraction gives the remainder. -/
theorem greedyAt_end {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) :
    greedyAt p len w (len + 1) = (resid p w : ℕ) := by
  obtain ⟨hlow, hhigh, hmod⟩ := greedyAt_inv hp hw (len + 1) le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at hhigh
  rw [resid_cast (by omega), ← Int.emod_eq_of_lt hlow hhigh]
  exact hmod

/-- Every number that resid holds is below 2^(len+1) p. -/
theorem greedyAt_lt {p len : ℕ} {w : ℤ} (hp : 1 ≤ p) (hw : |w| < 2 ^ len) {i : ℕ}
    (hi : i ≤ len + 1) : greedyAt p len w i < ((p * 2 ^ (len + 1) : ℕ) : ℤ) := by
  obtain ⟨-, hhigh, -⟩ := greedyAt_inv hp hw i hi
  exact hhigh.trans_le (by
    exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) (by omega)))

namespace Resid









end Resid














/-- **resid** returns w mod p and changes no cell.  It forms numbers up to 2^(len+1) p. -/
theorem resid_meets {μ : ℕ → ℤ} {pResid dbl p len : ℕ} {w : ℤ} (hP : P[pResid]? = some residBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p) (hseg : Seg μ dbl (dblList p len))
    (hlt : |w| < 2 ^ len) (hdbl : dbl + (len + 1) ≤ lim.space)
    (hword : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pResid d [w, dbl, len] μ (tResid len) fun r μ' => r = (resid p w : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have hlow := fun i hi => (greedyAt_inv hp hlt i hi).1
  have hhigh := fun i (hi : i ≤ len + 1) => greedyAt_lt hp hlt hi
  unfold tResid
  -- num := w + dbl[len]; exp := len + 1
  have hlow0 := hlow 0 (by omega)
  have hhigh0 := hhigh 0 (by omega)
  have hfirst : w + μ (dbl + len) = greedyAt p len w 0 := by rw [read_dblList hseg le_rfl, greedyAt]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (greedyAt p len w 0) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hfirst]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hfirst] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hfirst] <;> omega)));
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
          (len + 1 : ℕ)
            -- while 0 < exp.  Before round i, exp = len + 1 - i and num = greedyAt p len w i.
            
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
  -- while 0 < exp.  Before round i, exp = len + 1 - i and num = greedyAt p len w i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [w, dbl, len, (len + 1 - i : ℕ), greedyAt p len w i], μ⟩) (len + 1)
    (by simp) ?round ?done le_rfl) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hlowi := hlow i hi.le
    have hhighi := hhigh i hi.le
    have hread := read_dblList hseg (show len - i ≤ len by omega)
    have hexp : ((len + 1 - i : ℕ) : ℤ) - 1 = (len - i : ℕ) := by omega
    have hnext : len + 1 - (i + 1) = len - i := by omega
    have hpos : (0 : ℤ) ≤ ((p * 2 ^ (len - i) : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [hnext, greedyAt]
    generalize greedyAt p len w i = g at hlowi hhighi
    generalize ((p * 2 ^ (len - i) : ℕ) : ℤ) = q at hread hpos
    -- exp := exp - 1; if dbl[exp] ≤ num then num := num - dbl[exp]
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_, ?_⟩
    · simp [Limits.Addr, abs_le, hexp, hread]
      omega
    · by_cases hle : q ≤ g <;> simp [update_frame_setLocal, hexp, hread, hle]
  case done =>
    rintro _ rfl
    -- return num
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      Ends.setTo (greedyAt p len w (len + 1)) (by simp [greedyAt_end hp hlt])
      (hT := by simp; omega)⟩

/-! ## The residues of a list -/

namespace Residues











end Residues






































/-- One more residue. -/
theorem residList_take_succ (p : ℕ) {l : List ℤ} {i : ℕ} (hi : i < l.length) :
    residList p (l.take (i + 1)) = residList p (l.take i) ++ [resid p l[i]] := by
  rw [residList, residList, List.take_add_one, List.getElem?_eq_getElem hi, List.map_append]
  rfl

open Residues in
/-- **residues** writes the residues of a list and changes nothing else. -/
theorem residues_spec {μ : ℕ → ℤ} {pResid src dst m dbl p len U : ℕ} {l : List ℤ}
    (hP : P[pResid]? = some residBody) (hd : d < lim.depth)
    (pre : ResiduesPre lim μ src dst m dbl p len U l) :
    Ends lim P d (residuesBody pResid) ⟨frame [src, dst, m, dbl, len], μ⟩ (tResidues m len)
      fun σ' => SegN σ'.mem dst (residList p l) ∧ SameOutside μ σ'.mem dst m := by
  obtain ⟨hw, hp, segDbl, segSrc, rfl, hle, hlt, spaceDbl, spaceSrc, spaceDst, hm, apartSrc,
    apartDbl, hword⟩ := pre
  have hltZ : (U : ℤ) < 2 ^ len := by exact_mod_cast hlt
  unfold tResidues
  -- for i < m
  refine Ends.for (ResiduesInv μ src dst l.length dbl p len l) l.length (tResid len + 13)
    ?start ?round ?done ?bound
  case start =>
    exact ⟨0, μ, congrArg (fun loc => (⟨loc, μ⟩ : State))
      ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm), Seg.nil, .refl⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -, -⟩
    simp
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, seg, rest⟩
    have hread : μ' (src + i) = l[i] := (rest _ (by omega)).trans (segSrc.get hi)
    have hlen : (residList p (l.take i)).length = i := by simp [residList]; omega
    -- res := resid(src[i], dbl, len)
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
              ((resid_meets (w := l[i]) hP hw hp
                  (segDbl.keep
                    (by
                      ((try have := length_dblList);
                        (((try refine Light.SameOn.cell ?_);
                            (intro apspMacro_210470_0 apspMacro_210470_1);
                            (first
                              |
                                ((((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ =>
                                                    apspMacro_210470_2));
                                            ((try
                                                  have :=
                                                    apspMacro_210470_2
                                                      apspMacro_210470_0
                                                      (by omega)));
                                            (revert apspMacro_210470_2)));
                                      (intros);
                                      (try
                                          simp only [Function.update_apply,
                                            Light.wrote] at *)));
                                  (omega))
                              |
                                ((simp [length_dblList] at apspMacro_210470_1);
                                  (((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ =>
                                                    apspMacro_210470_3));
                                            ((try
                                                  have :=
                                                    apspMacro_210470_3
                                                      apspMacro_210470_0
                                                      (by omega)));
                                            (revert apspMacro_210470_3)));
                                      (intros);
                                      (try
                                          simp only [Function.update_apply,
                                            Light.wrote] at *)));
                                  (omega))
                              |
                                ((((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ =>
                                                    apspMacro_210470_4));
                                            ((try
                                                  have :=
                                                    apspMacro_210470_4
                                                      apspMacro_210470_0
                                                      (by omega)));
                                            (revert apspMacro_210470_4)));
                                      (intros);
                                      (try
                                          simp only [Function.update_apply,
                                            Light.wrote] at *)));
                                  (fail
                                      "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                its condition K x does not follow from the hypotheses."))))))))
                  ((hle.getElem hi).trans_lt hltZ) spaceDbl hword)
                _ (by omega))
              ?_ ?_ ?_ ?_
        |
          refine
            Light.Ends.callToThen
              (resid_meets (w := l[i]) hP hw hp
                (segDbl.keep
                  (by
                    ((try have := length_dblList);
                      (((try refine Light.SameOn.cell ?_);
                          (intro apspMacro_210470_5 apspMacro_210470_6);
                          (first
                            |
                              ((((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ =>
                                                  apspMacro_210470_7));
                                          ((try
                                                have :=
                                                  apspMacro_210470_7
                                                    apspMacro_210470_5 (by omega)));
                                          (revert apspMacro_210470_7)));
                                    (intros);
                                    (try
                                        simp only [Function.update_apply,
                                          Light.wrote] at *)));
                                (omega))
                            |
                              ((simp [length_dblList] at apspMacro_210470_6);
                                (((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ =>
                                                  apspMacro_210470_8));
                                          ((try
                                                have :=
                                                  apspMacro_210470_8
                                                    apspMacro_210470_5 (by omega)));
                                          (revert apspMacro_210470_8)));
                                    (intros);
                                    (try
                                        simp only [Function.update_apply,
                                          Light.wrote] at *)));
                                (omega))
                            |
                              ((((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ =>
                                                  apspMacro_210470_9));
                                          ((try
                                                have :=
                                                  apspMacro_210470_9
                                                    apspMacro_210470_5 (by omega)));
                                          (revert apspMacro_210470_9)));
                                    (intros);
                                    (try
                                        simp only [Function.update_apply,
                                          Light.wrote] at *)));
                                (fail
                                    "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                              SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                              its condition K x does not follow from the hypotheses."))))))))
                ((hle.getElem hi).trans_lt hltZ) spaceDbl hword)
              ?_ ?_ ?_ ?_);
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
      (on_goal -1 => omega);
      (on_goal -1 =>
          (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hread] <;> omega)));
      (on_goal -1 =>
          ((rintro _ μ₁
                ⟨rfl, rfl⟩
                    -- dst[i] := res
                    );
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    -- dst[i] := res
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (dst + i) (resid p l[i] : ℕ) ?_ ?_ ?_);
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
    refine ⟨by simp, resid p l[i],
      Function.update μ₁ (dst + i) (resid p l[i] : ℕ), by simp [update_frame_setLocal], ?_,
      rest.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := seg.snoc (resid p l[i])
    rwa [hlen, ← residList_take_succ p hi] at hsnoc
  case done =>
    rintro _ - ⟨r, μ', rfl, seg, rest⟩
    exact ⟨by simpa using seg, rest⟩

end Light.Sec3

end
end

section


/-!
# The count for one prime (proof of Theorem 17, "Hashing modulo a prime")

"For every prime p in the range we count the triples with S(a,b,c) ≡ 0 (mod p)", where S(a,b,c) =
w(a,b) + w(b,c) + w(a,c) is the weight of the triangle.  "Let P[a,c] := x^{w(a,c) mod p} and Q[c,b]
:= x^{w(b,c) mod p} be matrices over the ring ℤ[x]/(x^p - 1) […]; then F(p) + Z₀ is the sum over the
pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]."  Here F(p) is the number
of triples with S(a,b,c) ≠ 0 and p ∣ S(a,b,c), and Z₀ the number of triples with S(a,b,c) = 0.

countPrime(n, ab, bc, ac, p, len, K, N2, w) computes this count for one prime, in a work area at w.
Two letters of the quotation mean something else in the code.  There w is the address of the work
area, and the weights are the three lists ab, bc and ac.  And `P` is the program, while the matrices
P and Q occur only as the lists `matPList` and `matQList`.

The routine has three parts.

* The addresses of the parts of the work area (`cpAddr_spec`); they lie one behind the other
  (`cp_places`).
* Six tables: the doubles of p, the residues of the three lists of weights, the places of the
  Z-order, and the sizes 4^i p of the matrices of Strassen's recursion, which szTable(dst, p, J)
  writes (`szTable_spec`, `cpTables_spec`, `CpTabs`).
* The matrices P and Q in Z-order, their product by Strassen's algorithm, and the sum of the
  coefficients (`cpProduct_spec`).

`countPrime_spec` puts the three parts together.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/























namespace CountPrime





























end CountPrime
















































/-! ## The layout of the work area -/




























/-- The parts of the work area lie one behind the other; as one fact. -/
theorem cp_places (w len n K p : ℕ) :
    cpRab w len = w + (len + 1) ∧ cpRbc w len n = cpRab w len + n * n ∧
      cpRac w len n = cpRbc w len n + n * n ∧ cpMort w len n = cpRac w len n + n * n ∧
      cpSzt w len n K = cpMort w len n + 2 ^ K ∧ cpPm w len n K = cpSzt w len n K + (K + 1) ∧
      cpQm w len n K p = cpPm w len n K + 4 ^ K * p ∧
      cpRm w len n K p = cpQm w len n K p + 4 ^ K * p ∧
      cpScr w len n K p = cpRm w len n K p + 4 ^ K * p ∧
      w + countCells n p len K = cpScr w len n K p + strScr p K + (8 * (4 ^ K * p) + 1) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [cpScr, cpRm, cpQm, cpPm, cpSzt, cpMort, cpRac, cpRbc, cpRab, countCells]
  omega







/-- **The first part of countPrime**, in 50 steps. -/
theorem cpAddr_spec {μ : ℕ → ℤ} {n ab bc ac p len K w : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hp : 1 ≤ p) (hcells : w + countCells n p len K ≤ lim.space) :
    Ends lim P d cpAddr ⟨frame [n, ab, bc, ac, p, len, K, (2 ^ K : ℕ), w], μ⟩ 50 fun σ' =>
      σ' = ⟨frame (cpFrame n ab bc ac p len K w), μ⟩ := by
  have hplaces := cp_places w len n K p
  have hsq : ((2 ^ K : ℕ) : ℤ) * ((2 ^ K : ℕ) : ℤ) = ((4 ^ K : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← mul_pow]
    norm_num
  have hsize : ((4 ^ K : ℕ) : ℤ) * p = ((4 ^ K * p : ℕ) : ℤ) := by push_cast; ring
  have hle : 4 ^ K ≤ 4 ^ K * p := Nat.le_mul_of_pos_right _ hp
  rw [cpFrame]
  generalize 4 ^ K * p = size at *
  generalize 4 ^ K = F at *
  generalize 2 ^ K = N2 at *
  refine Ends.setToThen (n * n : ℕ) <| Ends.setToThen (cpRab w len) <|
    Ends.setToThen (cpRbc w len n) <| Ends.setToThen (cpRac w len n) <|
    Ends.setToThen (cpMort w len n) <| Ends.setToThen (cpSzt w len n K) <|
    Ends.setToThen size (he := by (((try have := Light.Std.space_le (by assumption)));
                                    ((try have := Light.Std.const_le (by assumption)));
                                    (simp [Light.Limits.Addr, abs_le, -abs_mul, hsq, hsize] <;> omega))) <|
    Ends.setToThen (cpPm w len n K) <| Ends.setToThen (cpQm w len n K p) <|
    Ends.setToThen (cpRm w len n K p) <| Ends.setTo (cpScr w len n K p) rfl

/-! ## What countPrime assumes -/

















/-- A list of residues is as long as the list of numbers. -/
@[simp] theorem length_residList (p : ℕ) (l : List ℤ) : (residList p l).length = l.length := by
  simp [residList]

/-- Residues modulo p are below p. -/
theorem lt_of_mem_residList {p : ℕ} (hp : 1 ≤ p) {l : List ℤ} {x : ℕ} (hx : x ∈ residList p l) :
    x < p := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact resid_lt (by omega) w

section Premise

variable {μ : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}

/-- The constant 4 fits in a word. -/
theorem CountPrimePre.four_le_word (pre : CountPrimePre lim d μ x p len K w) :
    (4 : ℤ) ≤ lim.word := by
  refine le_trans ?_ pre.wordStr
  have : 1 ≤ 16 ^ K * p := Nat.mul_pos (by positivity) pre.p_pos
  exact_mod_cast (by omega : 4 ≤ 4 * (16 ^ K * p))

/-- The size of a matrix fits in a word. -/
theorem CountPrimePre.size_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((4 ^ K * p : ℕ) : ℤ) ≤ lim.word := by
  have hle : 4 ^ K * p ≤ 16 ^ K * p := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) K)
  exact le_trans (by exact_mod_cast (by omega : 4 ^ K * p ≤ 4 * (16 ^ K * p))) pre.wordStr

/-- The number of entries of a matrix fits in a word. -/
theorem CountPrimePre.sq_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((2 ^ K * 2 ^ K : ℕ) : ℤ) ≤ lim.word := by
  rw [show 2 ^ K * 2 ^ K = 4 ^ K by rw [← mul_pow]; norm_num]
  exact le_trans (by exact_mod_cast Nat.le_mul_of_pos_right _ pre.p_pos) pre.size_le_word

/-- The entries of the table of doubles fit in a word. -/
theorem CountPrimePre.dbl_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word := by
  refine le_trans ?_ pre.wordDbl
  exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ len))

end Premise

/-! ## The procedures that countPrime calls -/

section meets

variable {μ : ℕ → ℤ}

/-- **dblTable** as a procedure. -/
theorem dblTable_meets {q dst p len : ℕ} (hP : P[q]? = some dblTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + (len + 1) ≤ lim.space)
    (hp : ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, len] μ (tDblTable len) fun _ μ' =>
      Seg μ' dst (dblList p len) ∧ SameOutside μ μ' dst (len + 1) :=
  Meets.of_body hP (dblTable_spec hw hdst hp)

/-- **residues** as a procedure. -/
theorem residues_meets {q pResid src dst m dbl p len U : ℕ} {l : List ℤ}
    (hP : P[q]? = some (residuesBody pResid)) (hR : P[pResid]? = some residBody)
    (hd : d < lim.depth) (pre : ResiduesPre lim μ src dst m dbl p len U l) :
    Meets lim P q d [src, dst, m, dbl, len] μ (tResidues m len) fun _ μ' =>
      SegN μ' dst (residList p l) ∧ SameOutside μ μ' dst m :=
  Meets.of_body hP (residues_spec hR hd pre)

end meets

/-! ## The tables -/










section parts

variable {ν : CpNums} {μ₀ μ μ' : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}

/-- The tables stay in their places when only cells behind them change. -/
theorem CpTabs.keep (tabs : CpTabs μ x p len K w) (pre : CountPrimePre lim d μ₀ x p len K w)
    (hs : Kept μ μ' (cpPm w len x.n K) := by ((try refine Light.SameOn.cell ?_);
                                                 (intro apspMacro_218347_0 apspMacro_218347_1);
                                                 (first
                                                   |
                                                     ((((repeat
                                                               (((with_reducible
                                                                       rename Light.SameOn _ _ _ => apspMacro_218347_2));
                                                                 ((try
                                                                       have :=
                                                                         apspMacro_218347_2 apspMacro_218347_0 (by omega)));
                                                                 (revert apspMacro_218347_2)));
                                                           (intros);
                                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                                       (omega))
                                                   |
                                                     ((simp [] at apspMacro_218347_1);
                                                       (((repeat
                                                               (((with_reducible
                                                                       rename Light.SameOn _ _ _ => apspMacro_218347_3));
                                                                 ((try
                                                                       have :=
                                                                         apspMacro_218347_3 apspMacro_218347_0 (by omega)));
                                                                 (revert apspMacro_218347_3)));
                                                           (intros);
                                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                                       (omega))
                                                   |
                                                     ((((repeat
                                                               (((with_reducible
                                                                       rename Light.SameOn _ _ _ => apspMacro_218347_4));
                                                                 ((try
                                                                       have :=
                                                                         apspMacro_218347_4 apspMacro_218347_0 (by omega)));
                                                                 (revert apspMacro_218347_4)));
                                                           (intros);
                                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                                       (fail
                                                           "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                     SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                     its condition K x does not follow from the hypotheses."))))) : CpTabs μ' x p len K w := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have lenM := length_spreadList (2 ^ K)
  (obtain ⟨⟩ := id pre.inst)
  exact ⟨tabs.dbl.keep, tabs.rab.keep, tabs.rbc.keep, tabs.rac.keep, tabs.mort.keep,
    tabs.szt.keep⟩

/-- What a call of residues from countPrime assumes: the list l of weights at src lies below the
work area, the table of doubles is written, and the residues go to dst, behind that table. -/
theorem CountPrimePre.residuesPre (pre : CountPrimePre lim d μ₀ x p len K w)
    {src dst : ℕ} {l : List ℤ} (segDbl : Seg μ w (dblList p len)) (segSrc : Seg μ src l)
    (hlen : l.length = x.n * x.n) (hle : AbsLe l x.U) (hsrc : src + x.n * x.n ≤ w)
    (hdst : w + (len + 1) ≤ dst) (hend : dst + x.n * x.n ≤ lim.space) :
    ResiduesPre lim μ src dst (x.n * x.n) w p len x.U l := by
  have cells := pre.cells
  exact ⟨pre.space_le, pre.p_pos, segDbl, segSrc, hlen, hle, pre.hU, by omega, by omega, hend,
    by omega, Or.inr (by omega), Or.inr (by omega), pre.wordDbl⟩

open CountPrime in
/-- **The second part of countPrime** writes the six tables. -/
theorem cpTables_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ x p len K w) :
    Ends lim P d (cpTables ν) ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w), μ⟩
      (tDblTable len + 3 * tResidues (x.n * x.n) len + (30 * 2 ^ K + 17) + tSzTable K + 35)
      fun σ' => ∃ (r : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w ++ [r]), μ'⟩ ∧
          CpTabs μ' x p len K w ∧ SameOutside μ μ' w (countCells x.n p len K) := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have lenM := length_spreadList (2 ^ K)
  have cells := pre.cells
  have depth := pre.depth
  (obtain ⟨⟩ := id pre.inst)
  -- the table of doubles
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
            ((dblTable_meets (dst := w) ctx.hDbl pre.space_le (by omega)
                pre.dbl_le_word)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (dblTable_meets (dst := w) ctx.hDbl pre.space_le (by omega)
              pre.dbl_le_word)
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
        ((rintro _ μ₁
              ⟨dbl₁, rest₁⟩
                  -- the residues of the list ab
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the residues of the list ab
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
            ((residues_meets ctx.hResidues ctx.hResid (by omega)
                (pre.residuesPre (dst := cpRab w len) dbl₁ pre.inst.segAB.keep
                  pre.inst.lenAB pre.inst.leAB pre.inst.belowAB (by omega)
                  (by omega)))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (residues_meets ctx.hResidues ctx.hResid (by omega)
              (pre.residuesPre (dst := cpRab w len) dbl₁ pre.inst.segAB.keep
                pre.inst.lenAB pre.inst.leAB pre.inst.belowAB (by omega)
                (by omega)))
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
        ((rintro _ μ₂
              ⟨rab₂, rest₂⟩
                  -- the residues of the list bc
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the residues of the list bc
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
            ((residues_meets ctx.hResidues ctx.hResid (by omega)
                (pre.residuesPre (dst := cpRbc w len x.n) dbl₁.keep
                  pre.inst.segBC.keep pre.inst.lenBC pre.inst.leBC
                  pre.inst.belowBC (by omega) (by omega)))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (residues_meets ctx.hResidues ctx.hResid (by omega)
              (pre.residuesPre (dst := cpRbc w len x.n) dbl₁.keep
                pre.inst.segBC.keep pre.inst.lenBC pre.inst.leBC pre.inst.belowBC
                (by omega) (by omega)))
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
        ((rintro _ μ₃
              ⟨rbc₃, rest₃⟩
                  -- the residues of the list ac
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the residues of the list ac
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
            ((residues_meets ctx.hResidues ctx.hResid (by omega)
                (pre.residuesPre (dst := cpRac w len x.n) dbl₁.keep
                  pre.inst.segAC.keep pre.inst.lenAC pre.inst.leAC
                  pre.inst.belowAC (by omega) (by omega)))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (residues_meets ctx.hResidues ctx.hResid (by omega)
              (pre.residuesPre (dst := cpRac w len x.n) dbl₁.keep
                pre.inst.segAC.keep pre.inst.lenAC pre.inst.leAC pre.inst.belowAC
                (by omega) (by omega)))
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
        ((rintro _ μ₄
              ⟨rac₄, rest₄⟩
                  -- the table of places
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the table of places
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
            ((spreadTable_meets (dst := cpMort w len x.n) ctx.hSpread pre.space_le
                pre.four_le_word pre.sq_le_word (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (spreadTable_meets (dst := cpMort w len x.n) ctx.hSpread pre.space_le
              pre.four_le_word pre.sq_le_word (by omega))
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
        ((rintro _ μ₅
              ⟨mort₅, rest₅⟩
                  -- the table of sizes
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the table of sizes
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
            ((szTable_meets (dst := cpSzt w len x.n K) ctx.hSz pre.space_le
                pre.four_le_word (by omega) pre.size_le_word)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (szTable_meets (dst := cpSzt w len x.n K) ctx.hSz pre.space_le
              pre.four_le_word (by omega) pre.size_le_word)
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
        ((rintro r μ₆
              ⟨szt₆, rest₆⟩
                  -- Each call has written behind the tables that were there.
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- Each call has written behind the tables that were there.
  exact ⟨r, μ₆, rfl, ⟨dbl₁.keep, rab₂.keep, rbc₃.keep, rac₄.keep, mort₅.keep, szt₆⟩,
    by ((try refine Light.SameOn.cell ?_);
         (intro apspMacro_221760_0 apspMacro_221760_1);
         (first
           |
             ((((repeat
                       (((with_reducible
                               rename Light.SameOn _ _ _ => apspMacro_221760_2));
                         ((try
                               have :=
                                 apspMacro_221760_2 apspMacro_221760_0 (by omega)));
                         (revert apspMacro_221760_2)));
                   (intros);
                   (try simp only [Function.update_apply, Light.wrote] at *)));
               (omega))
           |
             ((simp [] at apspMacro_221760_1);
               (((repeat
                       (((with_reducible
                               rename Light.SameOn _ _ _ => apspMacro_221760_3));
                         ((try
                               have :=
                                 apspMacro_221760_3 apspMacro_221760_0 (by omega)));
                         (revert apspMacro_221760_3)));
                   (intros);
                   (try simp only [Function.update_apply, Light.wrote] at *)));
               (omega))
           |
             ((((repeat
                       (((with_reducible
                               rename Light.SameOn _ _ _ => apspMacro_221760_4));
                         ((try
                               have :=
                                 apspMacro_221760_4 apspMacro_221760_0 (by omega)));
                         (revert apspMacro_221760_4)));
                   (intros);
                   (try simp only [Function.update_apply, Light.wrote] at *)));
               (fail
                   "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                             SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                             its condition K x does not follow from the hypotheses."))))⟩

/-! ## The product and the count -/

/-- What a call of buildZ from countPrime assumes: the residues R stand at r, one of the three lists
of residues, and the matrix goes to dst, behind the tables. -/
theorem CountPrimePre.buildZPre (pre : CountPrimePre lim d μ₀ x p len K w)
    (tabs : CpTabs μ x p len K w) {dst r : ℕ} {l : List ℤ} (segR : SegN μ r (residList p l))
    (hlen : l.length = x.n * x.n) (hr : r + x.n * x.n ≤ cpMort w len x.n)
    (hdst : cpPm w len x.n K ≤ dst) (hend : dst + 4 ^ K * p ≤ cpScr w len x.n K p) :
    BuildZPre lim μ dst r (cpMort w len x.n) x.n K p (residList p l) := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have cells := pre.cells
  exact
    { space_le := pre.space_le
      res :=
        { len := by simp [hlen], seg := segR, lt := fun _ h => lt_of_mem_residList pre.p_pos h }
      table := { len := length_spreadList _, seg := tabs.mort }
      n_le := pre.hK ▸ Nat.le_pow_clog (by norm_num) x.n, p_pos := pre.p_pos, dst_le := by omega
      apartR := Or.inr (by omega), apartM := Or.inr (by omega) }

open CountPrime in
/-- **The third part of countPrime** returns the count. -/
theorem cpProduct_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ₀ x p len K w)
    (tabs : CpTabs μ x p len K w) (r : ℤ) :
    Ends lim P d (cpProduct ν) ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w ++ [r]), μ⟩
      (2 * buildZTime x.n (2 ^ K) p + strSteps p K + countZeroTime x.n + 36) fun σ' =>
        σ'.loc 0 = countOf x.n p x.AB x.BC x.AC ∧
          SameOutside μ σ'.mem w (countCells x.n p len K) := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have h4 := pre.four_le_word
  have hw := pre.space_le
  have cells := pre.cells
  have depth := pre.depth
  have lenP := length_matPList x.n p K (residList p x.AC)
  -- the matrix P
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
            ((buildZ_P_meets ctx.hBuild
                (pre.buildZPre tabs (dst := cpPm w len x.n K) tabs.rac
                  pre.inst.lenAC (by omega) le_rfl (by omega)))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (buildZ_P_meets ctx.hBuild
              (pre.buildZPre tabs (dst := cpPm w len x.n K) tabs.rac
                pre.inst.lenAC (by omega) le_rfl (by omega)))
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
        ((rintro _ μ₁ ⟨segP, rest₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have tabs₁ : CpTabs μ₁ x p len K w := tabs.keep pre
  -- the matrix Q
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
            ((buildZ_Q_meets ctx.hBuild
                (pre.buildZPre tabs₁ (dst := cpQm w len x.n K p) tabs₁.rbc
                  pre.inst.lenBC (by omega) (by omega) (by omega)))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (buildZ_Q_meets ctx.hBuild
              (pre.buildZPre tabs₁ (dst := cpQm w len x.n K p) tabs₁.rbc
                pre.inst.lenBC (by omega) (by omega) (by omega)))
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
        ((rintro _ μ₂ ⟨segQ, rest₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have tabs₂ : CpTabs μ₂ x p len K w := tabs₁.keep pre
  -- the product
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
            ((strassen_spec ctx.str pre.space_le K
                { dst := cpRm w len x.n K p, a := cpPm w len x.n K, b := cpQm w len x.n K p
                  szt := cpSzt w len x.n K, p := p, scr := cpScr w len x.n K p, len := 4 ^ K * p, J := K
                  A := matPList x.n p K (residList p x.AC), B := matQList x.n p K (residList p x.BC)
                  α := 1, β := 1 } μ₂
                { size := rfl, prime := pre.p_pos
                  opA := { len := lenP, bound := absLe_matPList _ _ _ _, seg := segP.keep }
                  opB := { len := length_matQList _ _ _ _, bound := absLe_matQList _ _ _ _, seg := segQ }
                  table := { len := length_szList _ _, seg := tabs₂.szt }
                  word := by (rw [strassenBound_one_one]); (exact_mod_cast pre.wordStr) } _ (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (strassen_spec ctx.str pre.space_le K
              { dst := cpRm w len x.n K p, a := cpPm w len x.n K, b := cpQm w len x.n K p
                szt := cpSzt w len x.n K, p := p, scr := cpScr w len x.n K p, len := 4 ^ K * p, J := K
                A := matPList x.n p K (residList p x.AC), B := matQList x.n p K (residList p x.BC)
                α := 1, β := 1 } μ₂
              { size := rfl, prime := pre.p_pos
                opA := { len := lenP, bound := absLe_matPList _ _ _ _, seg := segP.keep }
                opB := { len := length_matQList _ _ _ _, bound := absLe_matQList _ _ _ _, seg := segQ }
                table := { len := length_szList _ _, seg := tabs₂.szt }
                word := by (rw [strassenBound_one_one]); (exact_mod_cast pre.wordStr) } _ (by omega))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil, ]);
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
        (((try have := Light.Std.space_le (by assumption))); ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 => ((rintro _ μ₃ ⟨segR, rest₃⟩); (try with_unfolding_none refine Light.Ends.skip ?_)))
  dsimp only at segR rest₃
  have tabs₃ : CpTabs μ₃ x p len K w := tabs₂.keep pre
  -- the count
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
            ((countZero_meets ctx.hCount (V := strassenBound p K 1 1)
                { space_le := pre.space_le
                  mat :=
                    { len := length_strassenList p K _ _ lenP (length_matQList _ _ _ _), seg := segR
                      bound :=
                        absLe_strassenList p K _ _ 1 1 (absLe_matPList _ _ _ _) (absLe_matQList _ _ _ _) (by norm_num)
                          (by norm_num) }
                  res :=
                    { len := by simp [pre.inst.lenAB], seg := tabs₃.rab
                      lt := fun _ h => lt_of_mem_residList pre.p_pos h }
                  table := { len := length_spreadList _, seg := tabs₃.mort }
                  n_le := pre.hK ▸ Nat.le_pow_clog (by norm_num) x.n, rm_lt := by omega
                  sum_le := by (rw [strassenBound_one_one]); (exact_mod_cast pre.wordSum) })
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (countZero_meets ctx.hCount (V := strassenBound p K 1 1)
              { space_le := pre.space_le
                mat :=
                  { len := length_strassenList p K _ _ lenP (length_matQList _ _ _ _), seg := segR
                    bound :=
                      absLe_strassenList p K _ _ 1 1 (absLe_matPList _ _ _ _) (absLe_matQList _ _ _ _) (by norm_num)
                        (by norm_num) }
                res :=
                  { len := by simp [pre.inst.lenAB], seg := tabs₃.rab
                    lt := fun _ h => lt_of_mem_residList pre.p_pos h }
                table := { len := length_spreadList _, seg := tabs₃.mort }
                n_le := pre.hK ▸ Nat.le_pow_clog (by norm_num) x.n, rm_lt := by omega
                sum_le := by (rw [strassenBound_one_one]); (exact_mod_cast pre.wordSum) })
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil, ]);
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
        (((try have := Light.Std.space_le (by assumption))); ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 => ((rintro _ μ₄ ⟨rfl, rfl⟩); (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨by simp [countOf, pre.hK], by ((try refine Light.SameOn.cell ?_);
                                           (intro apspMacro_225819_0 apspMacro_225819_1);
                                           (first
                                             |
                                               ((((repeat
                                                         (((with_reducible
                                                                 rename Light.SameOn _ _ _ => apspMacro_225819_2));
                                                           ((try
                                                                 have :=
                                                                   apspMacro_225819_2 apspMacro_225819_0 (by omega)));
                                                           (revert apspMacro_225819_2)));
                                                     (intros);
                                                     (try simp only [Function.update_apply, Light.wrote] at *)));
                                                 (omega))
                                             |
                                               ((simp [] at apspMacro_225819_1);
                                                 (((repeat
                                                         (((with_reducible
                                                                 rename Light.SameOn _ _ _ => apspMacro_225819_3));
                                                           ((try
                                                                 have :=
                                                                   apspMacro_225819_3 apspMacro_225819_0 (by omega)));
                                                           (revert apspMacro_225819_3)));
                                                     (intros);
                                                     (try simp only [Function.update_apply, Light.wrote] at *)));
                                                 (omega))
                                             |
                                               ((((repeat
                                                         (((with_reducible
                                                                 rename Light.SameOn _ _ _ => apspMacro_225819_4));
                                                           ((try
                                                                 have :=
                                                                   apspMacro_225819_4 apspMacro_225819_0 (by omega)));
                                                           (revert apspMacro_225819_4)));
                                                     (intros);
                                                     (try simp only [Function.update_apply, Light.wrote] at *)));
                                                 (fail
                                                     "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                               SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                               its condition K x does not follow from the hypotheses."))))⟩

/-- **countPrime** returns the count of the proof of Theorem 17 for the prime p, and changes only
cells of its work area. -/
theorem countPrime_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ x p len K w) :
    Ends lim P d (countPrimeBody ν) ⟨frame [x.n, x.ab, x.bc, x.ac, p, len, K, (2 ^ K : ℕ), w], μ⟩
      (countTime x.n p len K) fun σ' =>
        σ'.loc 0 = countOf x.n p x.AB x.BC x.AC ∧
          SameOutside μ σ'.mem w (countCells x.n p len K) := by
  unfold countTime
  -- the addresses
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen (cpAddr_spec pre.space_le pre.p_pos pre.cells) ?_
            ?_
      |
        refine
          Light.Ends.pieceLast (cpAddr_spec pre.space_le pre.p_pos pre.cells) ?_
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
    (on_goal -1 => rintro _ rfl)
  -- the tables
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (cpTables_spec ctx pre) ?_ ?_
      | refine Light.Ends.pieceLast (cpTables_spec ctx pre) ?_ ?_);
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
        rintro _
          ⟨r, μ₁, rfl, tabs, rest₁⟩
              -- the product and the count
              )
  -- the product and the count
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (cpProduct_spec ctx pre tabs r) ?_ ?_
      | refine Light.Ends.pieceLast (cpProduct_spec ctx pre tabs r) ?_ ?_);
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
    (on_goal -1 => rintro σ' ⟨hcount, rest₂⟩)
  exact ⟨hcount, rest₁.trans rest₂⟩

/-- **countPrime** as a procedure. -/
theorem countPrime_meets {q : ℕ} (hP : P[q]? = some (countPrimeBody ν)) (ctx : CpCtx P ν)
    (pre : CountPrimePre lim d μ x p len K w) :
    Meets lim P q d [x.n, x.ab, x.bc, x.ac, p, len, K, (2 ^ K : ℕ), w] μ (countTime x.n p len K)
      fun r μ' =>
        r = countOf x.n p x.AB x.BC x.AC ∧ SameOutside μ μ' w (countCells x.n p len K) :=
  Meets.of_body hP (countPrime_spec ctx pre)

end parts

/-! ## Larger primes need more cells and more time -/

/-- The work area grows with p. -/
theorem countCells_mono {p q : ℕ} (h : p ≤ q) (n len K : ℕ) :
    countCells n p len K ≤ countCells n q len K := by
  have hsize : 4 ^ K * p ≤ 4 ^ K * q := Nat.mul_le_mul_left _ h
  have hscr := strScr_mono h K
  unfold countCells
  omega

/-- The time grows with p. -/
theorem countTime_mono {p q : ℕ} (h : p ≤ q) (n len K : ℕ) :
    countTime n p len K ≤ countTime n q len K := by
  have hsize : 2 ^ K * 2 ^ K * p ≤ 2 ^ K * 2 ^ K * q := Nat.mul_le_mul_left _ h
  have hsteps := strSteps_mono h K
  unfold countTime buildZTime
  omega

end Light.Sec3

end
end

section


/-!
# The primes of the window (proof of Theorem 17)

The hashing of the proof of Theorem 17 uses "a prime p ∈ [√D/2, √D)".  primes(dst, D) lists these
primes in increasing order and returns their number (`primes_spec`).

* It computes s = ⌊√D⌋ and calls the sieve of Eratosthenes, which writes all primes up to s to dst.
  The sieve gets the s + 1 cells behind these s cells for its table.
* One pass keeps the primes p with D ≤ 4p² and p² < D and moves them to the front (`pass_spec`, with
  the round `keep_spec`).  What it keeps is the list of the window (`filter_primesBelow`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side -/







/-- The primes of the window are those of the primes up to ⌊√D⌋ that lie in the window. -/
theorem filter_primesBelow (D : ℕ) :
    inWindow D (Sieve.primesBelow (Nat.sqrt D + 1)) = primesList D := by
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) ?_ ?_ ?_
  · exact ((List.pairwise_le_range).filter _).filter _
  · exact (List.pairwise_le_range).filter _
  · refine (List.perm_ext_iff_of_nodup ((List.nodup_range.filter _).filter _)
      (List.nodup_range.filter _)).2 fun q => ?_
    refine Iff.trans ?_ (Spec.mem_primesList (D := D) (q := q)).symm
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, sq]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨Nat.lt_succ_of_le (Nat.le_sqrt.2 h.2.2.le), h.1⟩, h.2⟩⟩

theorem mul_self_le_of_mem_primesBelow {D p : ℕ} (hp : p ∈ Sieve.primesBelow (Nat.sqrt D + 1)) :
    p * p ≤ D :=
  Nat.le_sqrt.1 (Nat.lt_succ_iff.1 (List.mem_range.1 (List.mem_filter.1 hp).1))

/-- There are at most s - 1 primes up to s. -/
theorem length_primesBelow_succ_le (s : ℕ) : (Sieve.primesBelow (s + 1)).length ≤ s - 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · simp [Sieve.primesBelow_one]
  · have := Sieve.length_primesBelow_add_two_le (i := s + 1) (by omega)
    omega

theorem inWindow_take_succ_of_mem {D j : ℕ} {L : List ℕ} (hj : j < L.length) (h : InWindow D L[j]) :
    inWindow D (L.take (j + 1)) = inWindow D (L.take j) ++ [L[j]] := by
  unfold inWindow
  rw [List.take_succ_eq_append_getElem hj, List.filter_append,
    List.filter_cons_of_pos (by simpa using h), List.filter_nil]

theorem inWindow_take_succ_of_not_mem {D j : ℕ} {L : List ℕ} (hj : j < L.length)
    (h : ¬ InWindow D L[j]) : inWindow D (L.take (j + 1)) = inWindow D (L.take j) := by
  unfold inWindow
  rw [List.take_succ_eq_append_getElem hj, List.filter_append,
    List.filter_cons_of_neg (by simpa using h), List.filter_nil, List.append_nil]

/-! ## The program -/

namespace Primes













end Primes

open Primes




























namespace Primes

variable {μ : ℕ → ℤ} {dst D s : ℕ} {L : List ℕ}










/-- One round of the pass. -/
theorem keep_spec {j : ℕ} {σ : State} (hw : (lim.space : ℤ) ≤ lim.word)
    (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word) (hdst : dst + L.length ≤ lim.space)
    (hL : ∀ p ∈ L, p * p ≤ D) (hj : j < L.length) (h : Sifted μ dst D s L j σ) :
    Ends lim P d primesKeep σ primesKeep.blockCost (Sifted μ dst D s L (j + 1)) := by
  obtain ⟨μ', p₀, q₀, rfl, front, rest, same⟩ := h
  rw [List.drop_eq_getElem_cons hj] at rest
  obtain ⟨hread, hrest⟩ : μ' (dst + j) = (L[j] : ℕ) ∧ SegN μ' (dst + (j + 1)) (L.drop (j + 1)) :=
    seg_cons.1 rest
  have hcnt : (inWindow D (L.take j)).length ≤ j :=
    (List.length_filter_le _ _).trans (List.length_take_le _ _)
  have hsq : ((L[j] : ℕ) : ℤ) * (L[j] : ℕ) ≤ D := by exact_mod_cast hL _ (List.getElem_mem hj)
  have hsq0 : (0 : ℤ) ≤ ((L[j] : ℕ) : ℤ) * (L[j] : ℕ) := by positivity
  have hle : L[j] ≤ D := (Nat.le_mul_self _).trans (hL _ (List.getElem_mem hj))
  have htake := inWindow_take_succ_of_mem (D := D) hj
  have hpass := inWindow_take_succ_of_not_mem (D := D) hj
  unfold Sifted
  generalize L[j] = p at *
  generalize inWindow D (L.take j) = F at *
  push_cast at hD
  unfold primesKeep
  -- p := dst[j]; q := p * p; j := j + 1
  refine Ends.setToThen (p : ℕ) ?_ (by simp [Limits.Addr, abs_le, hread]; omega)
  refine Ends.setToThen (p * p : ℕ) ?_ (by simp [abs_le, -abs_mul]; omega)
  refine Ends.setToThen (j + 1 : ℕ) ?_
  -- if D ≤ 4 q and q < D
  refine Ends.iteLast (fun hlow => Ends.iteLast (fun hhigh => ?_) fun hnhigh => ?_) fun hnlow => ?_
  · have hin : InWindow D p :=
      ⟨by exact_mod_cast (by simpa [Cond.holds_le] using hlow : (D : ℤ) ≤ 4 * ((p : ℤ) * p)),
        by exact_mod_cast (by simpa using hhigh : (p : ℤ) * p < D)⟩
    rw [htake hin]
    -- dst[cnt] := p; cnt := cnt + 1
    refine Ends.storeToThen (dst + F.length) p ?_
    exact Ends.setTo (F.length + 1 : ℕ) ⟨Function.update μ' (dst + F.length) p, p, (p * p : ℕ),
      by simp, front.snoc p, hrest.update_out (Or.inl (by omega)) _,
      same.update ⟨by omega, by omega⟩ _⟩
  · rw [hpass fun hin => hnhigh (by simpa using (by exact_mod_cast hin.2 : (p : ℤ) * p < D))]
    exact Ends.skip ⟨μ', p, (p * p : ℕ), rfl, front, hrest, same⟩
  · rw [hpass fun hin => hnlow (by
      simpa [Cond.holds_le] using (by exact_mod_cast hin.1 : (D : ℤ) ≤ 4 * ((p : ℤ) * p)))]
    exact Ends.skip ⟨μ', p, (p * p : ℕ), rfl, front, hrest, same⟩

/-- The pass keeps the numbers of the list that lie in the window, and returns how many they are. -/
theorem pass_spec (hw : (lim.space : ℤ) ≤ lim.word) (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word)
    (hdst : dst + L.length ≤ lim.space) (hL : ∀ p ∈ L, p * p ≤ D) (seg : SegN μ dst L) :
    Ends lim P d primesPass ⟨frame [dst, D, s, L.length], μ⟩ (38 * L.length + 10) fun σ' =>
      σ'.loc 0 = ((inWindow D L).length : ℕ) ∧ SegN σ'.mem dst (inWindow D L) ∧
        SameOutside μ σ'.mem dst L.length := by
  -- cnt := 0; j := 0
  refine Ends.setToThen (0 : ℕ) (Ends.setToThen (0 : ℕ) ?_)
  -- while j < total
  refine Ends.next _ (Ends.whileConst (Sifted μ dst D s L) L.length primesKeep.blockCost ?start
    ?round ?done le_rfl) (by simp [primesKeep]; omega)
  case start =>
    exact ⟨μ, 0, 0, by simp, by rw [List.take_zero]; exact Seg.nil, by simpa using seg, .refl⟩
  case round =>
    rintro j σ hj h
    have hrun := keep_spec (P := P) (d := d) hw hD hdst hL hj h
    obtain ⟨μ', p, q, rfl, -⟩ := h
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), hrun⟩
  case done =>
    rintro _ h
    rw [Sifted, List.take_length] at h
    obtain ⟨μ', p, q, rfl, front, -, same⟩ := h
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- the result is cnt
    exact Ends.setTo ((inWindow D L).length : ℕ) ⟨by simp, front, same⟩ (by simp)
      (by simp [primesKeep]; omega)






/-- The square root, the sieve up to s, and a pass over n ≤ s - 1 primes. -/
theorem time_le {s n : ℕ} (hn : n ≤ s - 1) :
    18 * s + sieveTime s + 38 * n + 32 ≤ 80 * (s ^ 3 + 1) := by
  unfold sieveTime
  rcases Nat.lt_or_ge s 2 with hs | hs
  · interval_cases s <;> simp at hn ⊢ <;> omega
  · have hlog : 15 * s * (Nat.log 2 s + 5) ≤ 15 * s * (s + 4) :=
      Nat.mul_le_mul_left _ (by have := Nat.log_lt_self 2 (x := s) (by omega); omega)
    have hsq : 2 * (s * s) ≤ s ^ 3 := by
      rw [pow_succ, sq, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hs
    have hlin : 2 * s ≤ s * s := Nat.mul_le_mul_right _ hs
    have hmul : 15 * s * (s + 4) = 15 * (s * s) + 60 * s := by ring
    omega

end Primes

/-- **primes** writes the primes of the window, in increasing order, to dst, and returns their
number.  Only the 2 ⌊√D⌋ + 1 cells from dst may change. -/
theorem primes_spec {μ : ℕ → ℤ} {dst D pSqrt pSieve : ℕ} (C : Primes.Ctx P pSqrt pSieve)
    (hw : (lim.space : ℤ) ≤ lim.word) (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word)
    (hdst : dst + (2 * Nat.sqrt D + 1) ≤ lim.space) (hd : d < lim.depth) :
    Ends lim P d (primesBody pSqrt pSieve) ⟨frame [dst, D], μ⟩ (tPrimes D) fun σ' =>
      σ'.loc 0 = ((primesList D).length : ℕ) ∧ SegN σ'.mem dst (primesList D) ∧
        SameOutside μ σ'.mem dst (2 * Nat.sqrt D + 1) := by
  have hsD : Nat.sqrt D ≤ D := Nat.sqrt_le_self D
  have hL := fun p => mul_self_le_of_mem_primesBelow (D := D) (p := p)
  have hlen := length_primesBelow_succ_le (Nat.sqrt D)
  have htime := time_le hlen
  have hsqrt : Meets lim P pSqrt (d + 1) [D] μ (18 * Nat.sqrt D + 12) fun r μ' =>
      r = Nat.sqrt D ∧ μ' = μ :=
    sqrt_meets C.hSqrt μ (by push_cast at hD ⊢; omega)
  have hsieve := sieve_meets (μ := μ) (d := d + 1) (out := dst) (fr := dst + Nat.sqrt D) C.hSieve
    ⟨hw, by push_cast at hD ⊢; omega, le_rfl, by omega⟩
  rw [Sieve.sort_primesLE, ← Sieve.length_primesBelow] at hsieve
  rw [← filter_primesBelow D, tPrimes]
  generalize Sieve.primesBelow (Nat.sqrt D + 1) = L at *
  generalize Nat.sqrt D = s at *
  -- s := sqrt(D)
  refine Ends.callToThen hsqrt ?_
  rintro _ μ₀ ⟨rfl, hμ₀⟩
  obtain rfl : μ = μ₀ := hμ₀.symm
  -- total := sieve(s, dst, dst + s)
  refine Ends.callToThen hsieve ?_
  rintro _ μ₁ ⟨rfl, seg, kept⟩
  -- the pass
  refine (pass_spec hw hD (by omega) hL seg).mono (by first
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
                                                            | ((ring_nf); (omega)))) ?_
  rintro σ' ⟨hcount, front, same⟩
  exact ⟨hcount, front, kept.then same fun b hb => ⟨⟨by omega, by omega⟩, by omega⟩⟩

end Light.Sec3

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
# The parameters of Theorems 17 and 19 in integer arithmetic

The proof of Theorem 19 chooses `D` and `g` as rounded real powers of `n`: "Let D be the largest
power of four with D ≤ n^{1/18}, […] and let g := ⌈D^{1/36}⌉" on the route through Theorem 5, and
"Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉" on the route through Corollary 26.  The reduction of
Theorem 17 cuts each residue class into chunks of at most `n²/√D` query pairs and splits `C` into
pieces of at most `⌈s/g⌉` vertices, where `s = ⌊√D⌋`.  A program finds all these numbers by
operations on natural numbers.

* `rootFloor e t` is `⌊t^{1/e}⌋` and `rootCeil e t` is `⌈t^{1/e}⌉` (`floor_rpow_inv`,
  `ceil_rpow_inv`); they are characterised by `x ≤ rootFloor e t ↔ x^e ≤ t` (`le_rootFloor_iff`) and
  `rootCeil e t ≤ g ↔ t ≤ g^e` (`rootCeil_le_iff`).
* The four functions `paramD₅Nat`, `paramG₅Nat`, `paramD₂₆Nat`, `paramG₂₆Nat` are the parameters
  of the proof of Theorem 19 (`paramD₅Nat_eq`, `paramG₅Nat_eq`, `paramD₂₆Nat_eq`, `paramG₂₆Nat_eq`);
  they are at least 1 and at most `n` or `D` (`paramD₂₆Nat_le`, `paramG₅Nat_le`, `paramG₂₆Nat_le`).
* The sizes of the proof of Theorem 17: `⌊n²/√D⌋ = ⌊√(n⁴/D)⌋` (`queryCapNat_eq`), `s` is the integer
  square root (`sOf_eq_sqrt`), and the rounded quotients are `a ⌈/⌉ b` (`pieceSizeNat_eq`,
  `numPiecesNat_eq`, `numChunks_eq`).  The middle part `C_k × ℤ_p` of an instance has at most `D`
  vertices (`pieceSize_mul_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Roots, rounded down and up -/




















































/-! ## The parameters of the proof of Theorem 19 -/
















































































/-! ## The sizes of the instances of the proof of Theorem 17 -/



















/-- The test by which a program finds `queryCapNat n D`: `c + 1 ≤ ⌊n²/√D⌋` if and only if
`(c + 1)² D ≤ n⁴`. -/
theorem queryCapNat_succ_le_iff {n D : ℕ} (hD : 1 ≤ D) (c : ℕ) :
    c + 1 ≤ queryCapNat n D ↔ (c + 1) * (c + 1) * D ≤ n ^ 4 := by
  unfold queryCapNat
  rw [Nat.le_sqrt, Nat.le_div_iff_mul_le (by omega)]

/-- The largest number that this test forms. -/
theorem queryCapNat_succ_sq_mul_le {n D : ℕ} (hD : 1 ≤ D) :
    (queryCapNat n D + 1) * (queryCapNat n D + 1) * D ≤ 4 * n ^ 4 + D := by
  rcases Nat.eq_zero_or_pos (queryCapNat n D) with h | h
  · rw [h]
    omega
  · obtain ⟨c, hc⟩ : ∃ c, queryCapNat n D = c + 1 := ⟨queryCapNat n D - 1, by omega⟩
    have hle := (queryCapNat_succ_le_iff hD c).1 hc.ge
    rw [hc]
    calc (c + 1 + 1) * (c + 1 + 1) * D ≤ (2 * (c + 1)) * (2 * (c + 1)) * D :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
      _ = 4 * ((c + 1) * (c + 1) * D) := by ring
      _ ≤ 4 * n ^ 4 + D := by omega
































end ThreeSumApsp.Spec

end
end

section


/-!
# The prime that is chosen (proof of Theorem 17)

`chosenPrime n D AB BC AC` is the first prime of the window `√D/2 ≤ p < √D` at which the count,
computed with Strassen's algorithm from the three lists of weights, is smallest.  Here
`triOf n AB BC AC` is the instance of Exact Triangle whose weights are read from the three lists:
`w(a,b)` at `a n + b` of `AB`, `w(b,c)` at `b n + c` of `BC`, `w(a,c)` at `a n + c` of `AC`.

* The computed count is the count of the proof of Theorem 17 at every prime of the window
  (`countOf_eq`), so the chosen prime is a selected prime in the sense of the proof of Theorem 17,
  "We select the prime with the smallest count" (`chosenPrime_isSelected`).  It lies between 2 and
  `⌊√D⌋` (`two_le_chosenPrime`, `chosenPrime_le_sqrt`).
* A program finds it in one pass over the primes: `bestOf f L i` is the best of the first `i`
  elements of a list (`bestOf_one`, `bestOf_succ`, `bestOf_length`).
* The paper bounds the weights by `n^ν`; a program has a bound `U`.  `kappaOf n U` is the least
  exponent `κ ≥ 1` with `U ≤ n^κ`, and with it the bound of the proof of Theorem 17 on the number
  `F(p)` of false positives, that is, of triples with `S(a,b,c) ≠ 0` and `p ∣ S(a,b,c)`, holds for
  the chosen prime (`F_chosenPrime_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The chosen prime -/






section Chosen

variable {n D : ℕ} (AB BC AC : List ℤ)

/-- **The chosen prime is a selected prime** (proof of Theorem 17: "We select the prime with the
smallest count"). -/
theorem chosenPrime_isSelected (hD : 16 ≤ D) :
    (triOf n AB BC AC).IsSelectedPrime D (chosenPrime n D AB BC AC) := by
  -- The window has a prime `p₀`, so `List.argmin` returns `some m`, and the default 0 of
  -- `chosenPrime` is never used.
  obtain ⟨p₀, hp₀, -⟩ := TriangleInstance.exists_isSelectedPrime (triOf n AB BC AC) D hD
  rw [primesInRange_eq, List.mem_toFinset] at hp₀
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1
    (mt (List.argmin_eq_none (f := fun p => (countOf n p AB BC AC).toNat)).1
      (List.ne_nil_of_mem hp₀))
  -- The computed count is the count of the proof of Theorem 17 at every prime of the window.
  have hcount : ∀ q ∈ primesList D,
      (triOf n AB BC AC).countZeroMod q = (countOf n q AB BC AC).toNat := fun q hq => by
    rw [countOf_eq n AB BC AC (mem_primesList.1 hq).1.ne_zero, Int.toNat_natCast]
  rw [chosenPrime, hm, Option.getD_some, TriangleInstance.IsSelectedPrime, primesInRange_eq]
  refine ⟨List.mem_toFinset.2 (List.argmin_mem hm), fun q hq => ?_⟩
  rw [hcount m (List.argmin_mem hm), hcount q (List.mem_toFinset.1 hq)]
  exact List.le_of_mem_argmin (f := fun p => (countOf n p AB BC AC).toNat)
    (List.mem_toFinset.1 hq) hm

/-- The chosen prime is a prime of the window. -/
theorem chosenPrime_mem (hD : 16 ≤ D) : chosenPrime n D AB BC AC ∈ primesInRange D :=
  (chosenPrime_isSelected AB BC AC hD).1

/-- The chosen number is in the list of the primes of the window. -/
private theorem chosenPrime_mem_primesList (hD : 16 ≤ D) :
    chosenPrime n D AB BC AC ∈ primesList D := by
  have hmem := chosenPrime_mem (n := n) AB BC AC hD
  rwa [primesInRange_eq, List.mem_toFinset] at hmem





/-- The chosen prime is at most `⌊√D⌋`. -/
theorem chosenPrime_le_sqrt (hD : 16 ≤ D) : chosenPrime n D AB BC AC ≤ Nat.sqrt D :=
  le_sqrt_of_mem_primesList (chosenPrime_mem_primesList AB BC AC hD)

end Chosen

/-! ## The smallest count, by one pass -/




/-- The first element is the best of one. -/
theorem bestOf_one (f : ℕ → ℕ) (L : List ℕ) : bestOf f L 1 = L.getD 0 0 := by
  cases L <;> simp [bestOf]

/-- One more element: it is the best so far exactly if `f` is smaller there. -/
theorem bestOf_succ (f : ℕ → ℕ) (L : List ℕ) {i : ℕ} (hi : 1 ≤ i) (hiL : i < L.length) :
    bestOf f L (i + 1) = if f L[i] < f (bestOf f L i) then L[i] else bestOf f L i := by
  rw [bestOf, bestOf, List.take_succ_eq_append_getElem hiL, List.argmin_concat]
  cases h : (L.take i).argmin f with
  | none => exact absurd (List.argmin_eq_none.1 h) (List.ne_nil_of_length_pos (by simp; omega))
  | some c => simp only [Option.getD_some]; split_ifs <;> rfl

/-- The best of all the elements is what `List.argmin` returns. -/
theorem bestOf_length (f : ℕ → ℕ) (L : List ℕ) : (L.argmin f).getD 0 = bestOf f L L.length := by
  rw [bestOf, List.take_length]

/-! ## False positives, in terms of a bound on the weights -/











































end ThreeSumApsp.Spec

end
end

section


/-!
# The choice of the prime (proof of Theorem 17, "Hashing modulo a prime")

"We reduce the weights modulo a prime p ∈ [√D/2, √D), chosen deterministically. […] For every prime
p in the range we count the triples with S(a,b,c) ≡ 0 (mod p). […] We select the prime with the
smallest count".  Here S(a,b,c) is the weight of the triangle, the sum of its entries in the three
lists of weights ab, bc and ac, and D is the parameter of Theorem 17.

choosePrime(n, U, ab, bc, ac, D, w), where w is the address of the work area, lists the primes of
the range (`primesList D`) at w, computes the number len of binary digits of U and the numbers
K = ⌈log₂ n⌉ and 2^K (`chLevel_spec`), and goes through the primes once.  A round counts for one
prime, by a call of countPrime with the work area behind the list of the primes, and keeps the prime
if it is the first one or its count is smaller than the best so far (`chKeep_spec`,
`chRound_spec`).

On the pure side, `bestOf f L i` is the first of the first i primes with the smallest count, one
more prime changes it as the program does (`BestSoFar.step`), and at the end it is the chosen prime
(`bestOf_length`).  `choosePrime_spec` is the whole routine.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/


















namespace ChoosePrime






















end ChoosePrime




























































/-! ## The pure side: the best prime so far -/

/-- The count is not negative: it is a number of triples. -/
theorem countOf_nonneg (n : ℕ) {p : ℕ} (hp : 1 ≤ p) (AB BC AC : List ℤ) :
    0 ≤ countOf n p AB BC AC := by
  rw [countOf_eq n AB BC AC (by omega)]
  exact Int.natCast_nonneg _








/-- One more prime: it is kept if it is the first one or its count is smaller. -/
theorem BestSoFar.step {c : ℕ → ℤ} {L : List ℕ} {i : ℕ} {best cnt : ℤ}
    (h : BestSoFar c L i best cnt) (hi : i < L.length) (hc : 0 ≤ c L[i]) :
    BestSoFar c L (i + 1) (if i = 0 ∨ c L[i] < cnt then (L[i] : ℕ) else best)
      (if i = 0 ∨ c L[i] < cnt then c L[i] else cnt) := by
  refine Or.inr ⟨Nat.succ_pos i, ?_⟩
  obtain ⟨rfl, -⟩ | ⟨hi1, rfl, rfl, hcnt⟩ := h
  · rw [show bestOf (fun q => (c q).toNat) L (0 + 1) = L[0] from
      (bestOf_one _ L).trans (List.getD_eq_getElem _ _ hi)]
    simp [hc]
  · have hcmp : (c L[i]).toNat < (c (bestOf (fun q => (c q).toNat) L i)).toNat ↔
        c L[i] < c (bestOf (fun q => (c q).toNat) L i) := by omega
    rw [bestOf_succ _ L hi1 hi]
    simp only [hcmp, show i ≠ 0 by omega, false_or]
    split_ifs <;> simp [hc, hcnt]

/-! ## The parts of the program -/





section parts

variable {ν : ChNums} {μ μ' : ℕ → ℤ} {n U ab bc ac D w nP len K : ℕ} {AB BC AC : List ℤ}

/-- **K = ⌈log₂ n⌉ and 2^K.** -/
theorem chLevel_spec (hword : ((2 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d chLevel ⟨frame [n, U, ab, bc, ac, D, w, nP, len], μ⟩ (12 * Nat.clog 2 n + 8)
      fun σ' => σ' = ⟨frame [n, U, ab, bc, ac, D, w, nP, len, (Nat.clog 2 n : ℕ),
        (2 ^ Nat.clog 2 n : ℕ)], μ⟩ := by
  have test : ∀ j, 2 ^ j < n ↔ j < Nat.clog 2 n := fun j =>
    (Nat.lt_clog_iff_pow_lt (by norm_num)).symm
  generalize Nat.clog 2 n = L at test
  push_cast at hword
  -- level := 0; rows := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
          (1 : ℕ)
            -- while rows < n: rows := rows + rows; level := level + 1.  Before round j, rows = 2^j.
            
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
  -- while rows < n: rows := rows + rows; level := level + 1.  Before round j, rows = 2^j.
  refine Ends.whileBlock
    (fun j σ => σ = ⟨frame [n, U, ab, bc, ac, D, w, nP, len, j, (2 ^ j : ℕ)], μ⟩) L (by simp) ?round
    ?done
  case round =>
    rintro j _ hj rfl
    have hlt := (test j).2 hj
    have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
    rw [pow_succ, Nat.mul_two]
    generalize 2 ^ j = q at hlt hjlt
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hnot := mt (test L).1 (lt_irrefl L)
    generalize 2 ^ L = q at hnot
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), rfl⟩

/-- **Keeping the better prime.** -/
theorem chKeep_spec (h0 : 0 ≤ lim.word) (i : ℕ) (q c best cnt : ℤ) :
    Ends lim P d chKeep ⟨frame (chFrame n U ab bc ac D w nP len K i q c best cnt), μ⟩ 12 fun σ' =>
      σ' = ⟨frame (chFrame n U ab bc ac D w nP len K i q c
        (if i = 0 ∨ c < cnt then q else best) (if i = 0 ∨ c < cnt then c else cnt)), μ⟩ := by
  refine Ends.block ⟨by simp [chKeep, h0], ?_⟩ (by simp [chKeep])
  by_cases hi : i = 0 <;> by_cases hc : c < cnt <;>
    simp [chKeep, update_frame_setLocal, hi, hc]

variable {x : TriInst}

/-- The cells that choosePrime may change lie in the memory: the list of the primes, and the work
area of countPrime. -/
theorem ChoosePrimePre.cells_le (pre : ChoosePrimePre lim d μ x D w) :
    w + (Nat.sqrt D + countCells x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n)) ≤ lim.space :=
  pre.cells

/-- What countPrime assumes holds for each prime q of the range, with the work area behind the list
of the primes, as long as only cells from w on have changed. -/
theorem ChoosePrimePre.countPre (pre : ChoosePrimePre lim d μ x D w)
    (rest : SameOutside μ μ' w (chooseCells x.n x.U D)) {q : ℕ} (hq : q ∈ primesList D) :
    CountPrimePre lim (d + 1) μ' x q (bitLen x.U) (Nat.clog 2 x.n) (w + (primesList D).length) := by
  have cells := pre.cells_le
  have depth := pre.depth
  have hprimes := length_primesList_le D
  have hqS : q ≤ Nat.sqrt D := le_sqrt_of_mem_primesList hq
  have hcells := countCells_mono hqS x.n (bitLen x.U) (Nat.clog 2 x.n)
  exact
    { space_le := pre.space_le, inst := pre.inst.keep.mono (Nat.le_add_right _ _)
      p_pos := (mem_primesList.1 hq).1.one_le, hK := rfl, hU := Nat.lt_size_self x.U
      cells := by omega
      wordDbl := le_trans (by exact_mod_cast Nat.mul_le_mul_right _ hqS) pre.wordDbl
      wordStr := le_trans
        (by exact_mod_cast Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ hqS)) pre.wordStr
      wordSum := le_trans
        (by exact_mod_cast Nat.mul_le_mul_left (x.n * x.n) (Nat.mul_le_mul_left _ hqS)) pre.wordSum
      depth := by omega }










open ChoosePrime in
/-- **One round of choosePrime.** -/
theorem chRound_spec (ctx : ChCtx P ν) (pre : ChoosePrimePre lim d μ x D w) {i : ℕ}
    (hi : i < (primesList D).length) {σ : State} (h : ChInv μ x D w i σ) :
    Ends lim P d (chRound ν) σ (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 28)
      fun σ' => σ'.loc Idx = i ∧ ChInv μ x D w (i + 1)
        { σ' with loc := Function.update σ'.loc Idx ((i : ℤ) + 1) } := by
  obtain ⟨q₀, c₀, best, cnt, μ', rfl, hbest, seg, rest⟩ := h
  have hw := pre.space_le
  have cells := pre.cells_le
  have depth := pre.depth
  have hprimes := length_primesList_le D
  have hmem : (primesList D)[i] ∈ primesList D := List.getElem_mem hi
  have htime := countTime_mono (le_sqrt_of_mem_primesList hmem) x.n (bitLen x.U) (Nat.clog 2 x.n)
  have hcells :=
    countCells_mono (le_sqrt_of_mem_primesList hmem) x.n (bitLen x.U) (Nat.clog 2 x.n)
  have hread : μ' (w + i) = ((primesList D)[i] : ℕ) := by
    rw [seg i (by simpa using hi), List.getElem_map]
  -- prime := w[i]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen ((primesList D)[i] : ℕ) ?_ ?_ ?_);
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
  -- count := countPrime(n, ab, bc, ac, prime, len, K, 2^K, area)
  refine Ends.callToThen (countPrime_meets ctx.hCountPrime ctx.cp (pre.countPre rest hmem)) ?_
    (hT := by simp; omega)
  rintro _ μ'' ⟨rfl, rest'⟩
  -- The prime is kept if it is the first one or its count is smaller.
  refine (chKeep_spec (by omega) i _ _ best cnt).mono (by simp; omega) ?_
  rintro _ rfl
  refine ⟨by simp, ((primesList D)[i] : ℕ), countOf x.n (primesList D)[i] x.AB x.BC x.AC, _, _,
    μ'', by simp [update_frame_setLocal],
    hbest.step hi (countOf_nonneg x.n (mem_primesList.1 hmem).1.one_le x.AB x.BC x.AC),
    seg.keep, rest.trans (rest'.mono (by omega) ?_)⟩
  unfold chooseCells
  omega

/-- **primes** as a procedure. -/
theorem primes_meets {q dst pSqrt pSieve : ℕ} (hP : P[q]? = some (primesBody pSqrt pSieve))
    (C : Primes.Ctx P pSqrt pSieve) (hw : (lim.space : ℤ) ≤ lim.word)
    (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word) (hdst : dst + (2 * Nat.sqrt D + 1) ≤ lim.space)
    (hd : d < lim.depth) :
    Meets lim P q d [dst, D] μ (tPrimes D) fun r μ' =>
      r = ((primesList D).length : ℕ) ∧ SegN μ' dst (primesList D) ∧
        SameOutside μ μ' dst (2 * Nat.sqrt D + 1) :=
  Meets.of_body hP (primes_spec C hw hD hdst hd)

/-- **bitLen** as a procedure. -/
theorem bitLen_meets {q : ℕ} (hP : P[q]? = some bitLenBody)
    (hU : ((2 * U + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [U] μ (tBitLen U) fun r μ' => r = (bitLen U : ℕ) ∧ μ' = μ :=
  Meets.of_body hP (bitLen_spec hU)

open ChoosePrime in
/-- **choosePrime** returns the first prime of the range with the smallest count (0 if the range has
no prime), and changes only cells of its work area. -/
theorem choosePrime_spec (ctx : ChCtx P ν) (pre : ChoosePrimePre lim d μ x D w) :
    Ends lim P d (choosePrimeBody ν) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, D, w], μ⟩
      (chooseTime x.n x.U D) fun σ' =>
        σ'.loc 0 = (chosenPrime x.n D x.AB x.BC x.AC : ℕ) ∧
          SameOutside μ σ'.mem w (chooseCells x.n x.U D) := by
  have hw := pre.space_le
  have cells := pre.cells_le
  have depth := pre.depth
  have hprimes := length_primesList_le D
  have hroom : Nat.sqrt D + 1 ≤ countCells x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) := by
    have hle : Nat.sqrt D ≤ 4 ^ Nat.clog 2 x.n * Nat.sqrt D :=
      Nat.le_mul_of_pos_left _ (by positivity)
    unfold countCells
    generalize 4 ^ Nat.clog 2 x.n * Nat.sqrt D = A at hle ⊢
    generalize 2 ^ Nat.clog 2 x.n = B
    omega
  have hloop : (primesList D).length *
      (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 36) ≤
      Nat.sqrt D * (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 50) :=
    Nat.mul_le_mul (length_primesList_le D) (by omega)
  unfold chooseTime
  -- primes := the primes of the range, at w
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
            ((primes_meets (dst := w) ctx.hPrimes ctx.primes pre.space_le
                pre.wordD (by omega) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (primes_meets (dst := w) ctx.hPrimes ctx.primes pre.space_le pre.wordD
              (by omega) (by omega))
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
        ((rintro _ μ₁
              ⟨rfl, seg, rest⟩
                  -- len := bitLen(U)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- len := bitLen(U)
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
            ((bitLen_meets ctx.hBitLen pre.wordU) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (bitLen_meets ctx.hBitLen pre.wordU) ?_ ?_ ?_ ?_);
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
        ((rintro _ μ₂ ⟨rfl, hμ⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hμ]
  -- K and 2^K
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (chLevel_spec pre.wordN) ?_ ?_
      | refine Light.Ends.pieceLast (chLevel_spec pre.wordN) ?_ ?_);
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
  -- area := w + primes; best := 0; bestCount := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (w + (primesList D).length : ℕ) ?_ ?_ ?_);
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
            -- for i < primes: one round
            
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
  -- for i < primes: one round
  refine Ends.next _ (Ends.for (ChInv μ x D w) (primesList D).length
    (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 28) ?start
    (fun i σ hi _ h => chRound_spec ctx pre hi h) ?done ?bound (hT := le_rfl))
    (by simp; ring_nf at hloop ⊢; omega)
  case start =>
    exact ⟨0, 0, 0, 0, μ₁, by simp [update_frame_setLocal], Or.inl ⟨rfl, rfl⟩, seg,
      rest.mono le_rfl (by unfold chooseCells; omega)⟩
  case bound =>
    rintro i _ - - ⟨q, c, best, cnt, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨q, c, best, cnt, μ', rfl, hbest, -, rest'⟩
    -- return best
    refine Ends.setTo best ⟨?_, rest'⟩ (hT := by simp; ring_nf at hloop ⊢; omega)
    change best = (((primesList D).argmin fun q => (countOf x.n q x.AB x.BC x.AC).toNat).getD 0 : ℕ)
    obtain ⟨hnil, rfl⟩ | ⟨hpos, rfl, -, -⟩ := hbest
    · rw [List.eq_nil_of_length_eq_zero hnil]
      rfl
    · rw [bestOf_length]

/-- **choosePrime** as a procedure. -/
theorem choosePrime_meets {q : ℕ} (hP : P[q]? = some (choosePrimeBody ν)) (ctx : ChCtx P ν)
    (pre : ChoosePrimePre lim d μ x D w) :
    Meets lim P q d [x.n, x.U, x.ab, x.bc, x.ac, D, w] μ (chooseTime x.n x.U D) fun r μ' =>
      r = (chosenPrime x.n D x.AB x.BC x.AC : ℕ) ∧ SameOutside μ μ' w (chooseCells x.n x.U D) :=
  Meets.of_body hP (choosePrime_spec ctx pre)

end parts

end Light.Sec3

end
end

section


/-!
# The parameters of Theorems 17 and 19, without division and without roots

The proof of Theorem 19 chooses D as "the largest power of four with D ≤ n^{1/18}"
and g := ⌈D^{1/36}⌉, or D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉; the reduction of Theorem 17 uses
⌊n²/√D⌋ and quotients rounded up.  The language has neither division nor roots, so all of these are
found by counting up.  A power is compared with a bound without forming a number above the bound
times the base.

* powLt(g, e, t), for g ≥ 1, returns 1 if g^e < t, and 0 if not (`powLt_meets`); what it holds after
  i factors is `capPow g t i`.
* rootCeil(e, t) returns the least g with g^e ≥ t (`rootCeil_meets`).
* The four parameters; 5 and 26 stand for the two routes of Theorem 19, through Theorem 5 and
  through Corollary 26.  d5(n) returns the largest power of four that is at most n^{1/18}, g5(D)
  returns ⌈D^{1/36}⌉, d26(n) returns ⌊n^{1/18}⌋, and g26(D) returns ⌈D^{0.0315}⌉; g5 and g26
  are for D ≥ 1 (`d5_spec`, `g5_spec`, `d26_spec`, `g26_spec`).
* queryCapNat(n, D) returns ⌊n²/√D⌋, and ceilDiv(a, b) returns ⌈a/b⌉ (`queryCapNat_meets`,
  `ceilDiv_meets`).

No routine touches the memory.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Comparing a power with a bound -/





























namespace PowLt









end PowLt


















































/-! ## Roots, rounded up -/

namespace RootCeil







end RootCeil






























































/-! ## The four parameters of the proof of Theorem 19 -/

































































































































































/-! ## ⌊n²/√D⌋ and quotients rounded up -/











/-- The numbers that the test of queryCapNat forms for a candidate c that is at most the result
C. -/
private theorem queryCapNat_test_bounds {n D C c : ℕ} (hD : 1 ≤ D)
    (hmax : (C + 1) * (C + 1) * D ≤ 4 * n ^ 4 + D) (hc : c ≤ C) :
    (c : ℤ) + 1 ≤ ((c : ℤ) + 1) * ((c : ℤ) + 1) ∧
      ((c : ℤ) + 1) * ((c : ℤ) + 1) ≤ ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ∧
      ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ≤ 4 * ((n ^ 4 : ℕ) : ℤ) + D := by
  have hmono : (c + 1) * (c + 1) * D ≤ (C + 1) * (C + 1) * D :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  exact ⟨by exact_mod_cast Nat.le_mul_of_pos_right (c + 1) (Nat.succ_pos c),
    by exact_mod_cast Nat.le_mul_of_pos_right ((c + 1) * (c + 1)) hD,
    by exact_mod_cast hmono.trans hmax⟩

/-- **queryCapNat** returns ⌊n²/√D⌋, for D ≥ 1. -/
theorem queryCapNat_meets {μ : ℕ → ℤ} {q n D : ℕ} (hP : P[q]? = some queryCapNatBody) (hD : 1 ≤ D)
    (hword : ((4 * n ^ 4 + D + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [n, D] μ (tQueryCapNat n D) fun r μ' => r = (queryCapNat n D : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have test : ∀ c : ℕ, c + 1 ≤ queryCapNat n D ↔
      ((c : ℤ) + 1) * ((c : ℤ) + 1) * D ≤ ((n ^ 4 : ℕ) : ℤ) := fun c =>
    (queryCapNat_succ_le_iff hD c).trans (by exact_mod_cast Iff.rfl)
  have bounds := fun c =>
    queryCapNat_test_bounds (c := c) hD (queryCapNat_succ_sq_mul_le (n := n) hD)
  unfold tQueryCapNat
  generalize queryCapNat n D = C at test bounds
  rw [show ((4 * n ^ 4 + D + 2 : ℕ) : ℤ) = 4 * ((n ^ 4 : ℕ) : ℤ) + D + 2 by push_cast; ring]
    at hword
  have hsq : (n : ℤ) * n ≤ ((n ^ 4 : ℕ) : ℤ) := by
    exact_mod_cast (show n * n ≤ n ^ 4 by
      rw [show n ^ 4 = n * n * (n * n) by ring]; exact Nat.le_mul_self (n * n))
  have hcube : (n : ℤ) * n * n ≤ ((n ^ 4 : ℕ) : ℤ) := by
    exact_mod_cast (show n * n * n ≤ n ^ 4 by
      rw [show n ^ 4 = n * n * (n * n) by ring]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_self n))
  have hfour : (n : ℤ) * n * n * n = ((n ^ 4 : ℕ) : ℤ) := by push_cast; ring
  have hsq0 : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  have hcube0 : (0 : ℤ) ≤ (n : ℤ) * n * n := by positivity
  generalize ((n ^ 4 : ℕ) : ℤ) = N at *
  -- n4 := n⁴; cand := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen N ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hfour]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hfour] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hfour] <;> omega)));
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
          (0 : ℕ)
            -- while (cand + 1)² D ≤ n4: cand := cand + 1
            
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
  -- while (cand + 1)² D ≤ n4: cand := cand + 1
  refine Ends.next _ (Ends.whileBlock (fun c σ => σ = ⟨frame [n, D, N, c], μ⟩) C (by simp) ?round
    ?done le_rfl)
  case round =>
    rintro c _ hc rfl
    have hb := bounds c hc.le
    have hle := (test c).1 hc
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hb := bounds C le_rfl
    have hnot := mt (test C).2 (Nat.not_succ_le_self C)
    -- return cand
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), Ends.setTo C (by simp)⟩














/-- **ceilDiv** returns ⌈a/b⌉, for b ≥ 1. -/
theorem ceilDiv_meets {μ : ℕ → ℤ} {q a b : ℕ} (hP : P[q]? = some ceilDivBody) (hb : 1 ≤ b)
    (hword : ((a + b + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [a, b] μ (tCeilDiv a b) fun r μ' => r = (a ⌈/⌉ b : ℕ) ∧ μ' = μ := by
  refine .of_body hP ?_
  have test : ∀ i, i < a ⌈/⌉ b ↔ i * b < a := fun i => Nat.lt_ceilDiv_iff hb
  unfold tCeilDiv
  generalize a ⌈/⌉ b = q at test
  -- cand := 0; prod := 0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
          (0 : ℕ)
            -- while prod < a: prod := prod + b; cand := cand + 1.  Before round i, prod = i b.
            
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
  -- while prod < a: prod := prod + b; cand := cand + 1.  Before round i, prod = i b.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [a, b, i, (i * b : ℕ)], μ⟩) q (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt := (test i).1 hi
    have hle : i ≤ i * b := Nat.le_mul_of_pos_right i hb
    rw [Nat.succ_mul]
    generalize i * b = m at hlt hle
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hnot := mt (test q).2 (lt_irrefl q)
    generalize q * b = m at hnot
    -- return cand
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), Ends.setTo q (by simp)⟩

end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the top procedure

The host procedure et17(n, U, ab, bc, ac, fr) decides Exact Triangle with the help of an arbitrary
solver of Lop-AE-SparseTri (proof of Theorem 17).  It computes the parameters `D` and `g` by two
procedures that are parameters of the construction, and `s = ⌊√D⌋`.  For small `n`
(`D < 16`, `n < D`, `g < 1` or `s < g`) it runs the brute force.  Otherwise it chooses the prime,
computes the largest number of query pairs, the number of vertices of a piece and the number of
pieces, lays out its arrays from the free pointer on, computes the residues of the weights, sorts
the pairs `(a, b)` into classes, cuts the classes into chunks, and runs the loop over the instances.

This file holds the program (`et17Body`), its time and its need (`hostTime`, `hostNeed`), what it
assumes about the program around it (`Et17Ctx`), and the data, the addresses and the local variables
of a run.

**The way through the files on the host**, each named by its main result.

1. The instances as data, with no program in sight: what the host writes, what the solver answers
   and which scans succeed (`HostData`); a zero triangle is found if and only if there is one
   (`HostData.found_m`); a failed scan belongs to a false positive of its own
   (`HostData.sum_fails_le`); there are at most 4ng instances (`HostData.m_le`).
2. The loop over the instances (`hostLoop_spec`).
3. The text of the top procedure (this file), in three parts and the small case.
4. The parts: the parameters and the small case (`et17Params_spec`, `et17Small_spec`); the prime,
   the sizes and the addresses (`et17Sizes_spec`, `et17Addr_spec`); the arrays and the call of the
   loop (`et17Tables_spec`).
5. What the parts need: the limits cover what the called procedures ask for (`choosePre_of_ok`,
   `hostLim_of_ok`), and the time of a run is within the worst case (`hostRunTime_le`).
6. The parts together: et17 decides Exact Triangle (`et17_spec`).
7. The list of the procedures with their numbers; with a solver it is a solver (`et17Procs`,
   `et17_solves`).
8. For the claim: the need is polynomially bounded (`hostNeed_poly`), the time obeys the bound of
   Theorem 17 (`obeysBound17_hostTime`), and so the claim holds for programs of the light language
   (`claim17_of_host`, `claim_theorem_17₅`, `claim_theorem_17₂₆`).

The layout, from the free pointer `fr` on: the table of doubles (`len + 1` cells, where
`len = bitLen U` is the number of binary digits of `U`; cell `j` holds `2^j p`, for residues without
division); the residues of `w(a,b)`, `w(b,c)`, `w(a,c)` (`n²` each); the starts of the classes
(`p + 1`); running places (`p`; while the pairs are sorted, cell `ϱ` holds the next free place of
the class `ϱ`); rows and columns of the sorted pairs (`n²` each); the three components of the table
of chunks (`n² + p` each); `X` (`n D`); `Y` (`D n`); the answers (`cap`); the solver's free pointer.

Notation: `κ` is the exponent in `|w(e)| ≤ n^κ`, the paper's ν; as in the paper, `F(p)` is the
number of false positives of `p`, that is, of triples with `S(a,b,c) = w(a,b) + w(b,c) + w(a,c) ≠ 0`
and `p ∣ S(a,b,c)`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The procedure -/



























namespace Et17












































end Et17



































































/-! ## Time and need

The additive constants in the time functions are upper bounds for the cost of evaluating arguments,
of calls and of tests.  They are not meant to be tight. -/















































































/-! ## The context -/






























/-! ## The data, the addresses and the local variables of a run -/


































/-- The arrays of the host stand one after the other. -/
theorem host_places (X : HostData) (U fr : ℕ) :
    aRab X U fr = fr + (bitLen U + 1) ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCur X U fr = aCls X U fr + (X.p + 1) ∧ aQi X U fr = aCur X U fr + X.p ∧
      aQj X U fr = aQi X U fr + X.n * X.n ∧ aCr X U fr = aQj X U fr + X.n * X.n ∧
      aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧ aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧
      aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧ aY X U fr = aX X U fr + X.n * X.D ∧
      aOut X U fr = aY X U fr + X.n * X.D ∧ aFr X U fr = aOut X U fr + X.cap :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩







































end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the limits

The host procedure `et17` (Exact Triangle by Theorem 17) states what it needs of the limits of a
run: word size, memory, depth of calls (`hostNeedAt`).  This file shows that this need covers what
the procedures that it calls ask for.

* The arrays of the host lie one behind the other and fit into the cells that `hostLayout` counts
  (`aFr_le`).
* Every number that is at most `hostWord` fits in a word (`le_word_of_le_hostWord`).
* So the preconditions of the choice of the prime and of the loop over the instances hold
  (`choosePre_of_ok`, `hostLim_of_ok`).  For the solver this uses that an instance has at most
  `⌊n²/√D⌋` query pairs (`HostData.w_le_cap`, `need_le_supNeed`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The case that n is not small -/

/-- The host falls back on the brute force exactly if the hypotheses of Theorem 17 fail. -/
theorem not_smallCase_iff {n D g : ℕ} : ¬ SmallCase n D g ↔ BigCase n D g := by
  unfold SmallCase
  exact ⟨fun h => ⟨by omega, by omega, by omega, by omega⟩,
    fun ⟨_, _, _, _⟩ => by omega⟩

/-- The chosen prime is at most √D. -/
theorem hostData_p_le (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) :
    (hostData x D g).p ≤ Nat.sqrt D :=
  chosenPrime_le_sqrt x.AB x.BC x.AC hD
















/-! ## The addresses -/

/-- The free pointer of the solver, written out. -/
private theorem aFr_eq (X : HostData) (U fr : ℕ) :
    aFr X U fr = fr + (bitLen U + 1) + 3 * (X.n * X.n) + (X.p + 1) + X.p + 2 * (X.n * X.n)
      + 3 * (X.n * X.n + X.p) + 2 * (X.n * X.D) + X.cap := by
  simp only [aFr, aOut, aY, aX, aCw, aCl, aCr, aQj, aQi, aCur, aCls, aRac, aRbc, aRab]
  omega

/-- The arrays of et17 fit into the cells that hostLayout counts. -/
theorem aFr_le {x : TriInst} {D g : ℕ} (hD : 16 ≤ D) (fr : ℕ) :
    aFr (hostData x D g) x.U fr ≤ fr + hostLayout x.n x.U D := by
  have hp := hostData_p_le x g hD
  rw [aFr_eq]
  unfold hostLayout
  change fr + (bitLen x.U + 1) + 3 * (x.n * x.n) + ((hostData x D g).p + 1) + (hostData x D g).p
    + 2 * (x.n * x.n) + 3 * (x.n * x.n + (hostData x D g).p) + 2 * (x.n * D) + queryCapNat x.n D ≤ _
  omega

/-! ## The words -/

/-- The numbers of the host fit in a word. -/
private theorem hostWord_le {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {n U fr D g : ℕ}
    (hok : (hostNeedAt a b need n U D g).Ok lim fr d) :
    ((hostWord a b n U D g : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast Nat.le_add_right _ _) hok.word

/-- A number that is at most hostWord fits in a word. -/
theorem le_word_of_le_hostWord {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {n U fr D g : ℕ}
    (hok : (hostNeedAt a b need n U D g).Ok lim fr d) {z : ℕ}
    (hz : z ≤ hostWord a b n U D g := by unfold hostWord; omega) : ((z : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast hz) (hostWord_le hok)

/-- What choosePrime needs. -/
theorem choosePre_of_ok {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {x : TriInst} {μ : ℕ → ℤ}
    {fr D g : ℕ} (hpre : x.Pre μ fr) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    ChoosePrimePre lim (d + 1) μ x D fr := by
  have hcells : fr + (chooseCells x.n x.U D + hostLayout x.n x.U D
      + (supNeed need x.n D (queryCapNat x.n D)).cells + 2) ≤ lim.space := hok.cells
  have hdepth : d + (2 * Nat.clog 2 x.n + 8 + (supNeed need x.n D (queryCapNat x.n D)).depth)
      ≤ lim.depth := hok.depth
  exact
    { space_le := hok.space
      inst := hpre
      cells := by omega
      wordD := le_word_of_le_hostWord hok
      wordU := le_word_of_le_hostWord hok
      wordN := le_word_of_le_hostWord hok
      wordDbl := le_word_of_le_hostWord hok
      wordStr := le_word_of_le_hostWord hok
      wordSum := le_word_of_le_hostWord hok
      depth := by omega }













































end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the prime, the sizes, the addresses

This file proves the specification of the second part of the host procedure `et17` (Exact Triangle
by Theorem 17), which chooses the prime and computes the sizes and the addresses of the arrays:
five calls (`et17Sizes_spec`) and then seventeen assignments (`et17Addr_spec`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- **The sizes and the addresses.**  Of the locals that are set before, only Size, Free, ParD,
ThePrime, Cap and Bits are read. -/
theorem et17Addr_spec {μ : ℕ → ℤ} (x : TriInst) (X : HostData) {fr : ℕ} {g s : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (htop : aFr X x.U fr ≤ lim.space) :
    Ends lim P d et17Addr
      ⟨frame [(X.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (X.D : ℤ), g, s,
        (X.p : ℤ), (X.cap : ℤ), (X.q : ℤ), (X.h : ℤ), ((bitLen x.U : ℕ) : ℤ), 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], μ⟩
      et17Addr.blockCost fun σ' => σ' = ⟨frame (Et17.locals x X fr g s 0 0), μ⟩ := by
  have hplaces := host_places X x.U fr
  have hsquare : (0 : ℤ) ≤ (X.n : ℤ) * X.n := by positivity
  have harea : (0 : ℤ) ≤ (X.n : ℤ) * X.D := by positivity
  unfold et17Addr
  -- SizeSq := Size * Size ; Area := Size * ParD ; Room := SizeSq + ThePrime
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (X.n * X.n : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (X.n * X.D : ℕ) ?_ ?_ ?_);
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
          (X.n * X.n + X.p : ℕ)
            -- ResAB := Free + (Bits + 1) ; ResBC := ResAB + SizeSq ; ResAC := ResBC + SizeSq
            
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
  -- ResAB := Free + (Bits + 1) ; ResBC := ResAB + SizeSq ; ResAC := ResBC + SizeSq
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aRab X x.U fr) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (aRbc X x.U fr) ?_ ?_ ?_);
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
          (aRac X x.U fr)
            -- Cls := ResAC + SizeSq ; Cur := Cls + (ThePrime + 1) ; Rows := Cur + ThePrime
            
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
  -- Cls := ResAC + SizeSq ; Cur := Cls + (ThePrime + 1) ; Rows := Cur + ThePrime
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aCls X x.U fr) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (aCur X x.U fr) ?_ ?_ ?_);
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
          (aQi X x.U fr)
            -- Cols := Rows + SizeSq ; TabR := Cols + SizeSq ; TabL := TabR + Room ; TabW := TabL + Room
            
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
  -- Cols := Rows + SizeSq ; TabR := Cols + SizeSq ; TabL := TabR + Room ; TabW := TabL + Room
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aQj X x.U fr) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (aCr X x.U fr) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (aCl X x.U fr) ?_ ?_ ?_);
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
          (aCw X x.U fr)
            -- MatX := TabW + Room ; MatY := MatX + Area ; AdrOut := MatY + Area
            
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
  -- MatX := TabW + Room ; MatY := MatX + Area ; AdrOut := MatY + Area
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aX X x.U fr) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (aY X x.U fr) ?_ ?_ ?_);
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
          (aOut X x.U fr)
            -- SolverFree := AdrOut + Cap
            
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
  -- SolverFree := AdrOut + Cap
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aFr X x.U fr) ?_ ?_ ?_);
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














/-- The need of the host provides what the second part uses. -/
theorem sizesReady_of {need : List ℕ → Need} {x : TriInst} {fr D g a b : ℕ}
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    SizesReady lim d x fr D g := by
  have hD16 : 16 ≤ D := hbig.sixteen_le
  have hg1 : 1 ≤ g := hbig.one_le_g
  have hsqrt : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
  have hdepth := hok.depth
  have hcells := hok.cells
  have htop := aFr_le (x := x) (g := g) hD16 fr
  simp only [hostNeedAt] at hdepth hcells
  exact
    { one_le_D := by omega
      one_le_g := hg1
      one_le_piece := (Nat.lt_ceilDiv_iff hg1).2 (by omega)
      depth := by omega
      top := by omega
      wordCap := le_word_of_le_hostWord hok
      wordPiece := le_word_of_le_hostWord hok
      wordPieces := le_word_of_le_hostWord hok
      wordBits := le_word_of_le_hostWord hok }

/-- **The second part of et17**: the prime, the sizes and the addresses are in the locals; only
cells from the free pointer on have changed. -/
theorem et17Sizes_spec_sourceProof {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Sizes ν) ⟨frame (et17LocA x fr D g), μ⟩
      (chooseTime x.n x.U D + tQueryCapNat x.n D + tCeilDiv (Nat.sqrt D) g +
        tCeilDiv x.n (pieceSizeNat D g) + tBitLen x.U + 120)
      fun σ' => ∃ μ', σ' = ⟨frame (et17LocB x fr D g), μ'⟩ ∧ Kept μ μ' fr := by
  have hr := sizesReady_of (x := x) hbig hok
  have hdepth := hr.depth
  unfold et17Sizes et17LocA
  rw [if_neg (not_smallCase_iff.2 hbig)]
  -- ThePrime := pChoose(Size, Bound, AdrAB, AdrBC, AdrAC, ParD, Free)
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
            ((choosePrime_meets C.hChoose C.ch (choosePre_of_ok hpre hok)) _
              (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (choosePrime_meets C.hChoose C.ch (choosePre_of_ok hpre hok)) ?_ ?_ ?_
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
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro _ μ₁
              ⟨rfl, hμ₁⟩
                  -- Cap := pCap(Size, ParD)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- Cap := pCap(Size, ParD)
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
            ((queryCapNat_meets C.hCap hr.one_le_D hr.wordCap) _ (by omega)) ?_ ?_
            ?_ ?_
      |
        refine
          Light.Ends.callToThen (queryCapNat_meets C.hCap hr.one_le_D hr.wordCap)
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
        ((rintro _ μ₁
              ⟨rfl, rfl⟩
                  -- PieceLen := pCeil(RootD, ParG)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- PieceLen := pCeil(RootD, ParG)
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
            ((ceilDiv_meets C.hCeil hr.one_le_g hr.wordPiece) _ (by omega)) ?_ ?_
            ?_ ?_
      |
        refine
          Light.Ends.callToThen (ceilDiv_meets C.hCeil hr.one_le_g hr.wordPiece)
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
        ((rintro _ μ₁
              ⟨rfl, rfl⟩
                  -- NumPieces := pCeil(Size, PieceLen)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- NumPieces := pCeil(Size, PieceLen)
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
            ((ceilDiv_meets C.hCeil hr.one_le_piece hr.wordPieces) _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (ceilDiv_meets C.hCeil hr.one_le_piece hr.wordPieces) ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                pieceSizeNat]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [pieceSizeNat] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, pieceSizeNat] <;> omega)));
    (on_goal -1 =>
        ((rintro _ μ₁
              ⟨rfl, rfl⟩
                  -- Bits := pBitLen(Bound)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- Bits := pBitLen(Bound)
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
            ((bitLen_meets C.hBitLen hr.wordBits) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (bitLen_meets C.hBitLen hr.wordBits) ?_ ?_ ?_ ?_);
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
                  -- the sizes and the addresses
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the sizes and the addresses
  refine (et17Addr_spec x (hostData x D g) hok.space hr.top).mono (by simp [et17Addr]; omega) ?_
  rintro _ rfl
  exact ⟨μ₁, rfl, fun c hc => hμ₁ c (Or.inl hc)⟩

end Light.Sec3

end
end


theorem solution : ∀ {lim : Light.Limits} {d : Nat} {P₀ R : Light.Program} {ν : Light.Sec3.Et17Nums} {Tn : List.{0} Nat → Nat}
  {need : List.{0} Nat → Light.Need} {Dfun Gfun tD tG wD wG : Nat → Nat},
  Light.Sec3.Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG →
    ∀ (x : Light.TriInst) (μ : Nat → Int) (fr D g a b : Nat),
      x.Pre μ fr →
        Light.Sec3.BigCase x.n D g →
          (Light.Sec3.hostNeedAt a b need x.n x.U D g).Ok lim fr d →
            Light.Ends lim
              (@HAppend.hAppend.{0, 0, 0} Light.Program Light.Program Light.Program
                (@instHAppendOfAppend.{0} Light.Program (@List.instAppend.{0} Light.Stmt)) P₀ R)
              d (Light.Sec3.et17Sizes ν) { loc := Light.frame (Light.Sec3.et17LocA x fr D g), mem := μ }
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (Light.Sec3.chooseTime x.n x.U D)
                        (Light.Sec3.tQueryCapNat x.n D))
                      (Light.Sec3.tCeilDiv D.sqrt g))
                    (Light.Sec3.tCeilDiv x.n (ThreeSumApsp.Spec.pieceSizeNat D g)))
                  (Light.Sec3.tBitLen x.U))
                (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
              fun (σ' : Light.State) =>
              ∃ (μ' : Nat → Int),
                And (@Eq.{1} Light.State σ' { loc := Light.frame (Light.Sec3.et17LocB x fr D g), mem := μ' })
                  (Light.Kept μ μ' fr) := by
  exact @Light.Sec3.et17Sizes_spec_sourceProof

#print axioms solution
