-- Prove2me | solution 1 for Light.Sec3.et17_spec
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:40:23.295328+00:00
-- url     : https://prove2.me/submissions/50976d7f-48c9-4bd4-876c-4ea7f17d231d

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
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Chunks
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_ZOrder
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
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
import Mathlib.Combinatorics.Enumerative.DoubleCounting
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
import Theorems.Thm_Light_Sec3_et17Sizes_spec
import Theorems.Thm_Light_Sec3_et17Tables_spec
import Theorems.Thm_ThreeSumApsp_Spec_chunkTab_cover
import Theorems.Thm_ThreeSumApsp_Spec_chunkTab_pairwise
import Theorems.Thm_ThreeSumApsp_Spec_length_classIdx_eq_card
import Theorems.Thm_ThreeSumApsp_Spec_zRow_zCol_quadrant
import Theorems.Thm_ThreeSumApsp_TriangleInstance_card_instanceIndices

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

/-- Entry `j` of a list without its first `a` entries. -/
theorem getD_drop (l : List α) (a j : ℕ) (d : α) : (l.drop a).getD j d = l.getD (a + j) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Entry `j < n` of the first `n` entries. -/
theorem getD_take_of_lt (l : List α) {n j : ℕ} (hj : j < n) (d : α) :
    (l.take n).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]









































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

/-- Partial sums of natural numbers grow. -/
theorem sum_map_range_mono (g : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    ((List.range a).map g).sum ≤ ((List.range b).map g).sum := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _




























section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/






















/-- The members with `t a < z + 1` are those with `t a < z` and those with `t a = z`. -/
theorem length_filter_lt_succ (t : α → ℕ) (z : ℕ) (l : List α) :
    (l.filter fun a => decide (t a < z + 1)).length =
      (l.filter fun a => decide (t a < z)).length +
        (l.filter fun a => decide (t a = z)).length := by
  simp only [← List.countP_eq_length_filter]
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, ih, decide_eq_true_eq]
    split_ifs <;> omega











































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































































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_43568_0 apspMacro_43568_1);
                                                                                  (first
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_43568_2));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_43568_2 apspMacro_43568_0 (by omega)));
                                                                                                  (revert apspMacro_43568_2)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((simp [] at apspMacro_43568_1);
                                                                                        (((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_43568_3));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_43568_3 apspMacro_43568_0 (by omega)));
                                                                                                  (revert apspMacro_43568_3)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_43568_4));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_43568_4 apspMacro_43568_0 (by omega)));
                                                                                                  (revert apspMacro_43568_4)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (fail
                                                                                            "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                      its condition K x does not follow from the hypotheses."))))) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩



























































































































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











/-- Reading a cell. -/
theorem read (h : ListAt μ a l N top) (hi : i < N) : μ (a + i) = l.getD i 0 :=
  h.seg.getD (h.len ▸ hi) 0








end ListAt

namespace ArrayAt

/-- An array without the bound on its entries. -/
theorem listAt (h : ArrayAt μ a l N U top) : ListAt μ a l N top := { h with }












/-- Reading a cell. -/
theorem read (h : ArrayAt μ a l N U top) (hi : i < N) : μ (a + i) = l.getD i 0 := h.listAt.read hi












end ArrayAt









namespace IndexAt

variable {l : List ℕ} {p : ℕ}






















end IndexAt

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
















/-- A smaller need is allowed for if a larger one is, also with a larger free pointer and at a
larger depth if the sums are not larger. -/
theorem Need.Ok.mono {r r' : Need} {lim : Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (by exact_mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩








/-! ## Specifications of single routines -/






/-! ## Tasks and solvers -/
























































































/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/














































end Light

end
end

section


/-!
# The answer of a decision problem as a number

A routine for a decision problem returns 1 for yes and 0 for no: `flag p` is this number for the
proposition `p`.
-/

@[expose] public section

namespace ThreeSumApsp

















/-- Equivalent questions have the same answer. -/
theorem flag_congr {p q : Prop} (h : p ↔ q) : flag p = flag q := by
  rw [propext h]







end ThreeSumApsp

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
    (hs : Kept μ μ' fr := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_51110_0 apspMacro_51110_1);
                                 (first
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_51110_2));
                                                 ((try
                                                       have :=
                                                         apspMacro_51110_2 apspMacro_51110_0 (by omega)));
                                                 (revert apspMacro_51110_2)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((simp [] at apspMacro_51110_1);
                                       (((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_51110_3));
                                                 ((try
                                                       have :=
                                                         apspMacro_51110_3 apspMacro_51110_0 (by omega)));
                                                 (revert apspMacro_51110_3)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_51110_4));
                                                 ((try
                                                       have :=
                                                         apspMacro_51110_4 apspMacro_51110_0 (by omega)));
                                                 (revert apspMacro_51110_4)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (fail
                                           "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                     SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                     its condition K x does not follow from the hypotheses."))))) : x.Pre μ' fr := by
  (obtain ⟨⟩ := id h)
  exact { h with segAB := h.segAB.keep, segBC := h.segBC.keep, segAC := h.segAC.keep }































































































































































/-! ## The thin matrix product and the lopsided triangle problems -/




























































/-! The ten arguments of a procedure for one of these tasks, as local variables. -/

namespace ThinArg






















end ThinArg

























































end Light

end
end

section


/-!
# Scanning a piece (the proof of Theorem 17)

"For every query pair that the oracle accepts, scan the piece C_k of its instance for a c with
S(a,b,c) = 0".  The procedure scan (`scanBody`) goes through an interval of vertices `c` for a fixed
pair `(a, b)` (`scan_spec`, `scan_meets`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}




theorem flag_eq_bit (b : Bool) : flag (b = true) = bit b := by
  cases b
  · simp [bit, flag_of_not]
  · simp [bit, flag_of]

/-! ## The three arrays of weights -/










/-! ## Scanning an interval of vertices -/

namespace Scan


















end Scan





















/-- One more vertex in a scan. -/
theorem scanHit_succ (n : ℕ) (AB BC AC : List ℤ) (a b c0 c : ℕ) :
    scanHit n AB BC AC a b c0 (c + 1) = (scanHit n AB BC AC a b c0 c || decide
      (AB.getD (a * n + b) 0 + BC.getD (b * n + c0 + c) 0 + AC.getD (a * n + c0 + c) 0 = 0)) := by
  simp [scanHit, List.range_succ, List.any_append]

/-- One round of `scan`, for the weights `wbc` and `wac` that it reads. -/
theorem scanRound_runs {μ : ℕ → ℤ} {ab bc ac n a b c0 len c rowB rowA U : ℕ} {wab wbc wac : ℤ}
    {hit : Bool} (hw : (lim.space : ℤ) ≤ lim.word) (hU : 3 * (U : ℤ) + 1 ≤ lim.word)
    (hreadB : μ (rowB + c) = wbc) (hreadA : μ (rowA + c) = wac) (hB : rowB + c < lim.space)
    (hA : rowA + c < lim.space) (leAB : |wab| ≤ U) (leBC : |wbc| ≤ U) (leAC : |wac| ≤ U) :
    scanRound.Runs lim ⟨frame [ab, bc, ac, n, a, b, c0, len, c, bit hit, wab, rowB, rowA], μ⟩
      (· = ⟨frame [ab, bc, ac, n, a, b, c0, len, (c + 1 : ℕ),
        bit (hit || decide (wab + wbc + wac = 0)), wab, rowB, rowA], μ⟩) := by
  rw [abs_le] at leAB leBC leAC
  by_cases hz : wab + wbc + wac = 0 <;>
    exact ⟨by
      simp [scanRound, Limits.Addr, abs_le, update_frame_setLocal, hreadB, hreadA, hz]; omega,
      by simp [scanRound, update_frame_setLocal, hreadB, hreadA, hz, bit]⟩

/-- **scan** returns 1 if some `c` in the interval has `S(a,b,c) = 0`, and 0 if not; it changes no
cell. -/
theorem scan_spec {μ : ℕ → ℤ} {ab bc ac n a b c0 len U : ℕ} {AB BC AC : List ℤ}
    (C : Weights lim μ ab bc ac n U AB BC AC) (ha : a < n) (hb : b < n) (hc : c0 + len ≤ n) :
    Ends lim P d scanBody ⟨frame [ab, bc, ac, n, a, b, c0, len], μ⟩ (tScan len) fun σ' =>
      σ'.loc 0 = flag (scanHit n AB BC AC a b c0 len = true) ∧ σ'.mem = μ := by
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.arrAB); (obtain ⟨⟩ := id C.arrBC);
    (obtain ⟨⟩ := id C.arrAC))
  have iab : a * n + b < n * n := Nat.mul_add_lt_mul ha hb
  have ibc : b * n + (c0 + len) ≤ n * n := Nat.mul_add_le_mul hb hc
  have iac : a * n + (c0 + len) ≤ n * n := Nat.mul_add_le_mul ha hc
  -- The weight `w(a,b)` and the addresses of `w(b,c0)` and `w(a,c0)`.
  obtain ⟨wab, hwab⟩ : ∃ z, z = AB.getD (a * n + b) 0 := ⟨_, rfl⟩
  obtain ⟨rowB, hrowB⟩ : ∃ r, r = bc + b * n + c0 := ⟨_, rfl⟩
  obtain ⟨rowA, hrowA⟩ : ∃ r, r = ac + a * n + c0 := ⟨_, rfl⟩
  have hreadAB : μ (ab + (a * n + b)) = wab := (C.arrAB.read iab).trans hwab.symm
  have haddrAB : ((ab : ℤ) + (a : ℤ) * (n : ℤ) + (b : ℤ)).toNat = ab + (a * n + b) := by
    rw [show (ab : ℤ) + (a : ℤ) * (n : ℤ) + (b : ℤ) = ((ab + (a * n + b) : ℕ) : ℤ) by
      push_cast; ring, Int.toNat_natCast]
  have leAB : |wab| ≤ U := hwab ▸ AbsLe.abs_getD_le (Int.natCast_nonneg U) C.arrAB.bound _
  unfold scanBody tScan
  -- hit := 0; wab := ab[a n + b]; rowB := bc + b n + c0; rowA := ac + a n + c0; c := 0
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
    (refine Light.Ends.setToThen wab ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddrAB,
                hreadAB]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [haddrAB, hreadAB] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, haddrAB, hreadAB] <;>
              omega)));
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
    (refine Light.Ends.setToThen rowB ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen rowA ?_ ?_ ?_);
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
            -- while c < len
            
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
  -- while c < len
  refine Ends.next _ (Ends.whileBlock (fun c σ => σ = ⟨frame [ab, bc, ac, n, a, b, c0, len, c,
    bit (scanHit n AB BC AC a b c0 c), wab, rowB, rowA], μ⟩) len ?start ?round ?done le_rfl)
    (by simp [scanRound]; omega)
  case start => simp [scanHit, bit]
  case round =>
    rintro c _ hcl rfl
    have hreadBC : μ (rowB + c) = BC.getD (b * n + c0 + c) 0 := by
      rw [← C.arrBC.read (by omega), hrowB, Nat.add_assoc bc, Nat.add_assoc bc]
    have hreadAC : μ (rowA + c) = AC.getD (a * n + c0 + c) 0 := by
      rw [← C.arrAC.read (by omega), hrowA, Nat.add_assoc ac, Nat.add_assoc ac]
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    rw [scanHit_succ, ← hwab]
    exact scanRound_runs C.hw C.hU hreadBC hreadAC (by omega) (by omega) leAB
      (AbsLe.abs_getD_le (Int.natCast_nonneg U) C.arrBC.bound _)
      (AbsLe.abs_getD_le (Int.natCast_nonneg U) C.arrAC.bound _)
  case done =>
    rintro _ rfl
    -- return hit
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), Ends.setTo (bit (scanHit n AB BC AC a b c0 len))
      ⟨(flag_eq_bit _).symm, rfl⟩ (hT := by simp [scanRound]; omega)⟩

/-- The specification of `scan`, for its callers. -/
theorem scan_meets {p : ℕ} {μ : ℕ → ℤ} {ab bc ac n a b c0 len U : ℕ} {AB BC AC : List ℤ}
    (hP : P[p]? = some scanBody) (C : Weights lim μ ab bc ac n U AB BC AC) (ha : a < n) (hb : b < n)
    (hc : c0 + len ≤ n) :
    Meets lim P p d [ab, bc, ac, n, a, b, c0, len] μ (tScan len) fun r μ' =>
      r = flag (scanHit n AB BC AC a b c0 len = true) ∧ μ' = μ :=
  Meets.of_body hP (scan_spec C ha hb hc)

end Light.Sec3

end
end

section


/-!
# Reading the answers of one instance and scanning for witnesses

Proof of Theorem 17: "For every query pair that the oracle accepts, scan the piece C_k of its
instance for a c with S(a,b,c) = 0 [...].  We stop as soon as a zero triangle is found."

scanPairs(out, qa, qb, w, f, ab, bc, ac, n, c0, len): for every query pair number `i < w` whose
answer `out[i]` is not 0, scan the piece `{c0, …, c0 + len - 1}` for a zero triangle through the
pair `(qa[i], qb[i])`, as long as none has been found (`f = 0`).  The result is the new value of `f`
(`scanPairs_spec`).  No scan is made after the first successful one, so the number of scans is at
most the number of failed scans plus one (`execsUpto_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side -/

















theorem foundAt_zero (acc hit : ℕ → Bool) (f : Bool) : foundAt acc hit f 0 = f := by simp [foundAt]

theorem foundAt_succ (acc hit : ℕ → Bool) (f : Bool) (i : ℕ) :
    foundAt acc hit f (i + 1) = (foundAt acc hit f i || (acc i && hit i)) := by
  simp [foundAt, List.range_succ, Bool.or_assoc]

theorem execsUpto_succ (acc hit : ℕ → Bool) (f : Bool) (w : ℕ) :
    execsUpto acc hit f (w + 1) =
      execsUpto acc hit f w + (if execAt acc hit f w then 1 else 0) := by
  simp only [execsUpto, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split_ifs <;> rfl

theorem failsUpto_succ (acc hit : ℕ → Bool) (w : ℕ) :
    failsUpto acc hit (w + 1) = failsUpto acc hit w + (if acc w && !hit w then 1 else 0) := by
  simp only [failsUpto, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split_ifs <;> rfl

/-- **All scans but one fail.** -/
theorem execsUpto_le (acc hit : ℕ → Bool) (f : Bool) (w : ℕ) :
    execsUpto acc hit f w + f.toNat ≤ failsUpto acc hit w + (foundAt acc hit f w).toNat := by
  induction w with
  | zero => simp [execsUpto, failsUpto, foundAt_zero]
  | succ w ih =>
    rw [execsUpto_succ, failsUpto_succ, foundAt_succ, execAt]
    rcases ha : acc w <;> rcases hh : hit w <;> rcases hf : foundAt acc hit f w <;>
      simp [hf] at ih ⊢ <;> omega

/-! ## The routine -/

namespace ScanPairs

















end ScanPairs



































section

variable {pScan : ℕ} {μ : ℕ → ℤ} {out qa qb w ab bc ac n c0 len U : ℕ} {OUT AB BC AC : List ℤ}
  {QA QB : List ℕ} {f : Bool}

































































































end

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





/-- `a ⌈/⌉ b` pieces of size `b` overshoot `a` by less than one piece. -/
theorem ceilDiv_mul_lt {a b : ℕ} (hb : 0 < b) : a ⌈/⌉ b * b < a + b := by
  have := Nat.div_mul_le_self (a + b - 1) b
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega





/-- The ceiling of the real quotient of two natural numbers, in natural numbers. -/
theorem ceil_div_eq_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : ⌈(a : ℝ) / (b : ℝ)⌉₊ = a ⌈/⌉ b := by
  refine eq_of_forall_ge_iff fun k => ?_
  rw [Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.2 hb), ceilDiv_le_iff hb]
  exact_mod_cast Iff.rfl

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
# The table of the chunks (proof of Theorem 17)

"For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod p), and cut it into
chunks of at most n²/√D query pairs."  The routine lists the pairs class after class (`sortedIdx`).
Then a class is a segment of the list, from `classStart ϱ` to `classStart (ϱ + 1)`, and a chunk is a
segment of a class.  The table `chunkTab` has one entry for each chunk: its residue, the place where
it starts, and its number of pairs.

* The list has every pair once (`sortedIdx_nodup`, `classStart_eq_sq`), and the places of a class
  hold pairs of that class (`getD_sortedIdx_class`).
* An entry of the table is a nonempty segment of at most `cap` places (`chunkTab_entry`) whose pairs
  have the residue of the entry (`chunkTab_class`).
* The chunks follow each other (`chunkTab_pairwise`), so every place lies in exactly one chunk
  (`chunkTab_cover`, `chunkTab_unique`).
* "There are at most p + √D ≤ 2√D chunks in all" (`length_chunkTab_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

variable {n p cap : ℕ} {RAB : List ℕ}

/-! ## The classes and the list of all the pairs -/















/-- The places of a class. -/
theorem mem_classIdx {rho x : ℕ} : x ∈ classIdx n RAB rho ↔ x < n * n ∧ RAB.getD x 0 = rho := by
  simp [classIdx]

/-- The list holds places of pairs. -/
theorem lt_of_mem_sortedIdx {x : ℕ} (h : x ∈ sortedIdx n p RAB) : x < n * n := by
  obtain ⟨rho, -, hx⟩ := List.mem_flatMap.1 h
  exact (mem_classIdx.1 hx).1

/-- No pair is listed twice. -/
theorem sortedIdx_nodup (n p : ℕ) (RAB : List ℕ) : (sortedIdx n p RAB).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun rho _ => List.nodup_range.filter _, ?_⟩
  refine (List.nodup_range (n := p)).imp fun {a b} hab x hxa hxb => ?_
  exact hab ((mem_classIdx.1 hxa).2.symm.trans (mem_classIdx.1 hxb).2)

/-! ## The starts of the classes -/








/-- The next class starts where the class ends. -/
theorem classStart_succ (n : ℕ) (RAB : List ℕ) (rho : ℕ) :
    classStart n RAB (rho + 1) = classStart n RAB rho + (classIdx n RAB rho).length :=
  List.sum_range_succ _ _

/-- Later classes start later. -/
theorem classStart_mono (n : ℕ) (RAB : List ℕ) {a b : ℕ} (h : a ≤ b) :
    classStart n RAB a ≤ classStart n RAB b :=
  List.sum_map_range_mono _ h

/-- The list `classStarts` holds the starts of the classes. -/
theorem getD_classStarts_eq (n p : ℕ) (RAB : List ℕ) {rho : ℕ} (h : rho ≤ p) :
    (classStarts n p RAB).getD rho 0 = classStart n RAB rho :=
  List.getD_map_range _ (Nat.lt_succ_of_le h) 0

/-- The list of all the pairs ends where the class `p` would start. -/
theorem length_sortedIdx_eq (n p : ℕ) (RAB : List ℕ) :
    (sortedIdx n p RAB).length = classStart n RAB p :=
  List.length_flatMap

/-- The class `p` starts after the pairs with a residue below `p`. -/
theorem classStart_eq_length_filter (n : ℕ) (RAB : List ℕ) (p : ℕ) :
    classStart n RAB p =
      ((List.range (n * n)).filter fun i => decide (RAB.getD i 0 < p)).length := by
  induction p with
  | zero => simp [classStart]
  | succ p ih =>
    rw [classStart_succ, ih, List.length_filter_lt_succ fun i => RAB.getD i 0]
    rfl

/-- All the pairs are listed if all the residues are below `p`. -/
theorem classStart_eq_sq (hlt : ∀ i < n * n, RAB.getD i 0 < p) : classStart n RAB p = n * n := by
  rw [classStart_eq_length_filter, List.filter_eq_self.2, List.length_range]
  exact fun i hi => decide_eq_true (hlt i (List.mem_range.1 hi))












/-- The places from the start of the class `rho` to the start of the next class hold pairs with the
residue `rho`. -/
theorem getD_sortedIdx_class {rho j : ℕ} (hrho : rho < p) (hlo : classStart n RAB rho ≤ j)
    (hhi : j < classStart n RAB (rho + 1)) : RAB.getD ((sortedIdx n p RAB).getD j 0) 0 = rho := by
  rw [classStart_succ] at hhi
  obtain ⟨o, rfl⟩ := Nat.exists_eq_add_of_le hlo
  have ho : o < (classIdx n RAB rho).length := by omega
  rw [sortedIdx, classStart, List.getD_flatMap_range_sum _ hrho ho, List.getD_eq_getElem _ 0 ho]
  exact (mem_classIdx.1 (List.getElem_mem ho)).2

/-! ## The chunks -/






































/-- The table, in terms of the starts of the classes. -/
theorem chunkTab_eq (n p cap : ℕ) (RAB : List ℕ) :
    chunkTab n p cap RAB = (List.range p).flatMap fun rho =>
      (List.range ((classIdx n RAB rho).length ⌈/⌉ cap)).map (chunkAt n cap RAB rho) := by
  unfold chunkTab chunkTabOf
  refine List.flatMap_congr fun rho hrho => ?_
  have h := List.mem_range.1 hrho
  rw [getD_classStarts_eq n p RAB (by omega), getD_classStarts_eq n p RAB (by omega), chunksOf,
    classStart_succ, Nat.add_sub_cancel_left]
  rfl

/-- The entries of the table: chunk number `i` of the class `rho`. -/
theorem mem_chunkTab (x : Chunk) :
    x ∈ chunkTab n p cap RAB ↔
      ∃ rho < p, ∃ i < (classIdx n RAB rho).length ⌈/⌉ cap, x = chunkAt n cap RAB rho i := by
  simp only [chunkTab_eq, List.mem_flatMap, List.mem_range, List.mem_map, eq_comm (a := x)]

/-- An entry of the table has a residue below `p`, and it is a nonempty segment of at most `cap`
places of the list. -/
theorem chunkTab_entry (hcap : 1 ≤ cap) (hlt : ∀ i < n * n, RAB.getD i 0 < p) {x : Chunk}
    (hx : x ∈ chunkTab n p cap RAB) : x.Fits n p cap := by
  obtain ⟨rho, hrho, i, hi, rfl⟩ := (mem_chunkTab x).1 hx
  have hleft := (Nat.lt_ceilDiv_iff hcap).1 hi
  have hend := classStart_mono n RAB (show rho + 1 ≤ p by omega)
  rw [classStart_succ, classStart_eq_sq hlt] at hend
  constructor <;> simp only [chunkAt] <;> omega

/-- The pairs of a chunk have the residue of its entry. -/
theorem chunkTab_class (hcap : 1 ≤ cap) {x : Chunk} (hx : x ∈ chunkTab n p cap RAB) {i : ℕ}
    (hi : i < x.len) : RAB.getD ((sortedIdx n p RAB).getD (x.start + i) 0) 0 = x.residue := by
  obtain ⟨rho, hrho, i', hi', rfl⟩ := (mem_chunkTab x).1 hx
  have hleft := (Nat.lt_ceilDiv_iff hcap).1 hi'
  simp only [chunkAt] at hi ⊢
  exact getD_sortedIdx_class hrho (by omega) (by rw [classStart_succ]; omega)








































/-- A place lies in one chunk only. -/
theorem chunkTab_unique (hcap : 1 ≤ cap) {j k k' : ℕ} (h : k < (chunkTab n p cap RAB).length)
    (h' : k' < (chunkTab n p cap RAB).length) (hj : (chunkTab n p cap RAB)[k].Contains j)
    (hj' : (chunkTab n p cap RAB)[k'].Contains j) : k = k' := by
  have hpair := List.pairwise_iff_getElem.1 (chunkTab_pairwise (n := n) (p := p) (RAB := RAB) hcap)
  obtain ⟨hlo, hhi⟩ := hj
  obtain ⟨hlo', hhi'⟩ := hj'
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · have := hpair k k' h h' hlt
    omega
  · exact heq
  · have := hpair k' k h' h hgt
    omega

/-- The number of chunks, class by class. -/
theorem length_chunkTab (n p cap : ℕ) (RAB : List ℕ) :
    (chunkTab n p cap RAB).length =
      ((List.range p).map fun rho => (classIdx n RAB rho).length ⌈/⌉ cap).sum := by
  rw [chunkTab_eq, List.length_flatMap]
  simp




















end ThreeSumApsp.Spec

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





































































































/-- Proof of Theorem 17: "F(p) = [...] = O(ν n³ log n/√D)", with `Hashing.falsePositiveConst` as the
constant. -/
theorem Hashing.F_le_falsePositiveConst_mul {n D p : ℕ} {κ : ℝ} (hD : 16 ≤ D) (hDn : D ≤ n)
    (hκ : 1 ≤ κ) (T : TriangleInstance ℤ n) (hT : T.WeightsPolyBounded κ)
    (hp : T.IsSelectedPrime D p) :
    (T.F p : ℝ) ≤ Hashing.falsePositiveConst * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) :=
  (Classical.choose_spec TriangleInstance.exists_F_le).2 hD hDn hκ T hT hp

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











end ThreeSumApsp.Spec

end
end

section


/-!
# Cutting a set of pairs into chunks

Corollary 15 splits the query pairs "into sets of at most n²/√D query pairs", and the proof of
Theorem 17 cuts each set `W_ϱ` "into chunks of at most n²/√D query pairs".  In both, the chunk
number `j` of `S` holds the pairs of `S` whose rank in row-major order, divided by `cap`, is `j`.

* A chunk has at most `cap` pairs (`card_chunk_le`), because different pairs of `S` have different
  ranks (`rankIn_injOn`).
* The first `⌈|S|/cap⌉` chunks cover `S` (`biUnion_chunk`).
* In both uses `cap = ⌊n²/√D⌋`, which is at least 1 for `1 ≤ D ≤ n` (`one_le_queryCap`).
-/

public section

namespace ThreeSumApsp

variable {n : ℕ} {S : Finset (Fin n × Fin n)} {cap : ℕ}

/-! ### Ranks -/


























/-! ### Chunks -/

















/-! ### The size of the chunks in Corollary 15 and in Theorem 17 -/

/-- `√D ≤ D ≤ n`. -/
theorem sqrt_le_natCast {D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) : Real.sqrt D ≤ n :=
  calc Real.sqrt D ≤ Real.sqrt D * Real.sqrt D :=
        le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr (by exact_mod_cast hD))
    _ = D := Real.mul_self_sqrt (Nat.cast_nonneg D)
    _ ≤ n := by exact_mod_cast hDn

/-- The bound `⌊n²/√D⌋` on the size of a chunk is at least 1, because `√D ≤ n ≤ n²`. -/
theorem one_le_queryCap {D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) : 1 ≤ queryCap n D := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hD)), one_mul]
  exact (sqrt_le_natCast hD hDn).trans (le_self_pow₀ hn two_ne_zero)

end ThreeSumApsp

end
end

section


/-!
# Theorem 17, second step: the instances

With `s = ⌊√D⌋`, the part `C` is split into `h` pieces of at most `⌈s/g⌉` vertices, the pairs
`(a,b)` are grouped by `ϱ = w(a,b) mod p` into the sets `W_ϱ`, and every `W_ϱ` is cut into chunks of
at most `n²/√D` pairs.  There is one instance of Lop-AE-SparseTri(n, D) for each chunk and each
piece.  As in the paper:

* the pieces, and `h ≤ ⌈ng/s⌉` (`existsUnique_mem_piece`, `card_piece_le`,
  `numPieces_le`);
* the sets `W_ϱ` and their chunks (`TriangleInstance.existsUnique_mem_residueClass`,
  `TriangleInstance.card_chunkOf_le`);
* there are at most `p + √D ≤ 2√D` chunks in all (`TriangleInstance.totalChunks_le`); as a chunk
  holds a whole number of pairs, this rests on `n² < (s + 1)⌊n²/√D⌋ + p` (`sq_lt_mul_queryCap_add`);
* the middle part has at most `sp ≤ D` vertices (`TriangleInstance.middleAtMost_lopInstance`);
* within a chunk, `S(a,b,c) ≡ 0 (mod p)` is an equality of labels
  (`TriangleInstance.S_modEq_zero_iff`), so a query pair has a common neighbor if and only if some
  `c` in the piece has `S(a,b,c) ≡ 0 (mod p)` (`TriangleInstance.inTriangle_lopInstance_iff`);
* there are at most `2√D h ≤ 4ng` instances (`le_sOf_and_sqrt_le`,
  `TriangleInstance.card_instanceIndices_le`).

The file ends with a remark of Section 3.1 and of Remark 20: a vertex of `A` or `B` has at most
`⌈s/g⌉` neighbors in an instance (`TriangleInstance.ncard_nbr_lopInstance_le`).  Nothing else rests
on it.
-/

@[expose] public section

namespace ThreeSumApsp

variable {n D g p : ℕ}

/-! ### The pieces -/

/-- `s = ⌊√D⌋ ≤ √D`. -/
theorem sOf_le_sqrt (D : ℕ) : (sOf D : ℝ) ≤ Real.sqrt D := Nat.floor_le (Real.sqrt_nonneg _)

/-- `√D < s + 1`. -/
theorem sqrt_lt_sOf_add_one (D : ℕ) : Real.sqrt D < (sOf D : ℝ) + 1 := Nat.lt_floor_add_one _

/-- `s > 0` because `D ≥ 16`. -/
private theorem sOf_pos (hD : 16 ≤ D) : (0 : ℝ) < sOf D := by
  linarith [Real.four_le_sqrt_natCast_of_sixteen_le hD, sqrt_lt_sOf_add_one D]

/-- The bound `⌈s/g⌉` on the size of a piece is at least 1. -/
theorem pieceSize_pos (hD : 16 ≤ D) (hg1 : 1 ≤ g) : 0 < pieceSize D g :=
  Nat.ceil_pos.mpr (div_pos (sOf_pos hD) (by exact_mod_cast hg1))

























/-- Proof of Theorem 17: "so that h ≤ ⌈ng/s⌉". -/
theorem numPieces_le (hD : 16 ≤ D) (hg1 : 1 ≤ g) :
    numPieces n D g ≤ ⌈(n : ℝ) * (g : ℝ) / (sOf D : ℝ)⌉₊ := by
  have hsize : (0 : ℝ) < pieceSize D g := by exact_mod_cast pieceSize_pos hD hg1
  have hg : (0 : ℝ) < g := by exact_mod_cast hg1
  -- `s ≤ ⌈s/g⌉ g`
  have hs : (sOf D : ℝ) ≤ (pieceSize D g : ℝ) * (g : ℝ) := (div_le_iff₀ hg).mp (Nat.le_ceil _)
  refine Nat.ceil_mono ?_
  rw [div_le_div_iff₀ hsize (sOf_pos hD)]
  calc (n : ℝ) * (sOf D : ℝ) ≤ (n : ℝ) * ((pieceSize D g : ℝ) * (g : ℝ)) := by gcongr
    _ = (n : ℝ) * (g : ℝ) * (pieceSize D g : ℝ) := by ring

/-! ### Residues -/





/-- The residue of `x` is congruent to `x`. -/
theorem resFin_modEq (hp : p ≠ 0) (x : ℤ) : ((resFin hp x : ℕ) : ℤ) ≡ x [ZMOD (p : ℤ)] := by
  rw [resFin, Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp)]
  exact Int.mod_modEq x p

/-- An element of `Fin p` is congruent to `x` modulo `p` exactly if it is the residue of `x`. -/
private theorem modEq_iff_eq_resFin (hp : p ≠ 0) (σ : Fin p) (x : ℤ) :
    ((σ : ℕ) : ℤ) ≡ x [ZMOD (p : ℤ)] ↔ σ = resFin hp x := by
  refine ⟨fun h => ?_, fun h => h ▸ resFin_modEq hp x⟩
  -- Two congruent numbers in `{0, …, p − 1}` are equal.
  have hmod : (σ : ℕ) ≡ (resFin hp x : ℕ) [MOD p] :=
    (Int.natCast_modEq_iff).mp (h.trans (resFin_modEq hp x).symm)
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod σ.isLt (resFin hp x).isLt)

/-! ### The arithmetic behind the two counts -/

/-- The number `⌈|S|/cap⌉` of chunks of `S` satisfies `⌈|S|/cap⌉ cap ≤ |S| + cap − 1`. -/
private theorem numChunks_mul_le (S : Finset (Fin n × Fin n)) (cap : ℕ) (hcap : 1 ≤ cap) :
    numChunks S cap * cap + 1 ≤ S.card + cap := by
  rw [numChunks, Nat.ceil_div_eq_ceilDiv _ hcap]
  exact Nat.ceilDiv_mul_lt hcap

/-- `s + 1` exceeds `√D` by at least `1/(2√D + 1)`: since `(s + 1)²` and `D` are integers,
`1 ≤ (s + 1)² − D = (s + 1 − √D)(s + 1 + √D)`. -/
private theorem one_le_gap_mul (D : ℕ) :
    1 ≤ ((sOf D : ℝ) + 1 - Real.sqrt D) * (2 * Real.sqrt D + 1) := by
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt (Nat.cast_nonneg D)
  have hle := sOf_le_sqrt D
  have hlt := sqrt_lt_sOf_add_one D
  have hinteger : (D : ℝ) + 1 ≤ ((sOf D : ℝ) + 1) ^ 2 := by
    have hreal : (D : ℝ) < ((sOf D : ℝ) + 1) ^ 2 :=
      hsq ▸ pow_lt_pow_left₀ hlt (Real.sqrt_nonneg _) two_ne_zero
    have hnat : D < (sOf D + 1) ^ 2 := by exact_mod_cast hreal
    exact_mod_cast hnat
  calc (1 : ℝ) ≤ ((sOf D : ℝ) + 1) ^ 2 - Real.sqrt D ^ 2 := by linarith [hinteger, hsq]
    _ = ((sOf D : ℝ) + 1 - Real.sqrt D) * ((sOf D : ℝ) + 1 + Real.sqrt D) := by ring
    _ ≤ ((sOf D : ℝ) + 1 - Real.sqrt D) * (2 * Real.sqrt D + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- The inequality behind "at most p + √D [...] chunks": `n² < (s + 1) ⌊n²/√D⌋ + p`.

Write `r = √D`, `x = n²/r` and `δ = s + 1 − r`.  Then
`(s + 1)⌊x⌋ > (s + 1)(x − 1) = n² + xδ − (s + 1)`, so it is enough that `xδ ≥ r/2 + 1 ≥ s + 1 − p`.
This holds because `x ≥ r³` (as `D ≤ n`), `δ ≥ 1/(2r + 1)` (as `D` is an integer) and `r ≥ 4`. -/
private theorem sq_lt_mul_queryCap_add (hD : 16 ≤ D) (hDn : D ≤ n)
    (hp : Real.sqrt D / 2 ≤ (p : ℝ)) : n ^ 2 < (sOf D + 1) * queryCap n D + p := by
  have hgap := one_le_gap_mul D
  have hs := sOf_le_sqrt D
  set r := Real.sqrt D with hr
  set δ := (sOf D : ℝ) + 1 - r with hδ
  set x := (n : ℝ) ^ 2 / r with hx
  have hr4 : 4 ≤ r := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hxr : x * r = (n : ℝ) ^ 2 := div_mul_cancel₀ _ (by linarith)
  have hx3 : r ^ 3 ≤ x := by
    rw [hx, le_div_iff₀ (by linarith)]
    calc r ^ 3 * r = (r ^ 2) ^ 2 := by ring
      _ = (D : ℝ) ^ 2 := by rw [hr, Real.sq_sqrt (Nat.cast_nonneg D)]
      _ ≤ (n : ℝ) ^ 2 := by gcongr
  have hxδ : r / 2 + 1 ≤ x * δ := by
    refine le_of_mul_le_mul_right ?_ (show 0 < 2 * r + 1 by linarith)
    calc (r / 2 + 1) * (2 * r + 1) ≤ r ^ 3 := by
          -- `r³ ≥ 4r²` and `r² ≥ 4r`
          linarith [mul_le_mul_of_nonneg_right hr4 (sq_nonneg r),
            mul_le_mul_of_nonneg_right hr4 (show 0 ≤ r by linarith)]
      _ ≤ x * 1 := by rw [mul_one]; exact hx3
      _ ≤ x * (δ * (2 * r + 1)) :=
          mul_le_mul_of_nonneg_left hgap (le_trans (by positivity) hx3)
      _ = x * δ * (2 * r + 1) := by ring
  have hfloor : x < (queryCap n D : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmain : (n : ℝ) ^ 2 < ((sOf D : ℝ) + 1) * (queryCap n D : ℝ) + p :=
    calc (n : ℝ) ^ 2 = x * r := hxr.symm
      _ ≤ x * r + x * δ - ((sOf D : ℝ) + 1) + r / 2 := by
          -- `s + 1 ≤ r + 1 ≤ xδ + r/2`
          linarith [hxδ, hs]
      _ = ((sOf D : ℝ) + 1) * (x - 1) + r / 2 := by rw [hδ]; ring
      _ < ((sOf D : ℝ) + 1) * (queryCap n D : ℝ) + p :=
          add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (by linarith [hfloor]) (by positivity)) hp
  exact_mod_cast hmain

/-- Proof of Theorem 17: the two facts used for the count of the instances, "s ≥ √D − 1 ≥ 3√D/4
because D ≥ 16, and √D ≤ √n ≤ 2n/3 because D ≤ n and we may assume n ≥ 3". -/
theorem le_sOf_and_sqrt_le (hD : 16 ≤ D) (hDn : D ≤ n) :
    3 * Real.sqrt D / 4 ≤ (sOf D : ℝ) ∧ Real.sqrt D ≤ 2 * (n : ℝ) / 3 := by
  have hsqrtD := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hsqrtn := Real.four_le_sqrt_natCast_of_sixteen_le (hD.trans hDn)
  constructor
  · calc 3 * Real.sqrt D / 4 ≤ Real.sqrt D - 1 := by linarith
      _ ≤ (sOf D : ℝ) := by linarith [sqrt_lt_sOf_add_one D]
  · calc Real.sqrt D ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hDn)
      _ ≤ 2 * (n : ℝ) / 3 := by
          -- `n = √n √n ≥ 4√n`
          linarith [mul_le_mul_of_nonneg_right hsqrtn (Real.sqrt_nonneg n),
            Real.mul_self_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

namespace TriangleInstance

variable (T : TriangleInstance ℤ n)

/-! ### The sets `W_ϱ` -/

/-- A pair lies in `W_ϱ` exactly if `ϱ` is the residue of its weight. -/
theorem mem_residueClass (hp : p ≠ 0) (ϱ : Fin p) (q : Fin n × Fin n) :
    q ∈ T.residueClass p ϱ ↔ ϱ = resFin hp (T.wAB q.1 q.2) := by
  rw [← modEq_iff_eq_resFin]
  simp only [residueClass, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨Int.ModEq.symm, Int.ModEq.symm⟩








/-- The sets `W_ϱ` have `n²` pairs in all. -/
private theorem sum_card_residueClass (hp : p ≠ 0) :
    ∑ ϱ : Fin p, (T.residueClass p ϱ).card = n ^ 2 := by
  calc ∑ ϱ : Fin p, (T.residueClass p ϱ).card
      = ∑ ϱ : Fin p, ((Finset.univ : Finset (Fin n × Fin n)).filter
          fun q => resFin hp (T.wAB q.1 q.2) = ϱ).card := by
        refine Finset.sum_congr rfl fun ϱ _ => congrArg Finset.card ?_
        ext q
        rw [T.mem_residueClass hp]
        simp [eq_comm]
    _ = (Finset.univ : Finset (Fin n × Fin n)).card :=
        (Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)).symm
    _ = n ^ 2 := by simp [sq]

/-! ### The chunks -/









/-- There are at most `p + s` chunks in all.  Each `W_ϱ` has at most `(|W_ϱ| + cap − 1)/cap` chunks,
where `cap = ⌊n²/√D⌋`, so `p + s + 1` chunks or more would need `n² ≥ (s + 1) cap + p` pairs. -/
private theorem totalChunks_le_add_sOf (hD : 16 ≤ D) (hDn : D ≤ n) (hp0 : p ≠ 0)
    (hp : Real.sqrt D / 2 ≤ (p : ℝ)) : T.totalChunks D p ≤ p + sOf D := by
  have hsum : T.totalChunks D p * queryCap n D + p ≤ n ^ 2 + p * queryCap n D := by
    have h := Finset.sum_le_sum fun ϱ (_ : ϱ ∈ (Finset.univ : Finset (Fin p))) =>
      numChunks_mul_le (T.residueClass p ϱ) (queryCap n D) (one_le_queryCap (by omega) hDn)
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] at h
    rwa [T.sum_card_residueClass hp0] at h
  have hpairs := sq_lt_mul_queryCap_add hD hDn hp
  by_contra hmany
  have hmul : (p + sOf D + 1) * queryCap n D ≤ T.totalChunks D p * queryCap n D :=
    Nat.mul_le_mul_right _ (by omega)
  rw [show (p + sOf D + 1) * queryCap n D = p * queryCap n D + (sOf D + 1) * queryCap n D by
    ring] at hmul
  -- `hsum` and `hmul` give `(s + 1) cap + p ≤ n²`, against `hpairs`.
  omega

/-- Proof of Theorem 17: "There are at most p + √D ≤ 2√D chunks in all."

NOTE.  A chunk holds a whole number of pairs, at most `⌊n²/√D⌋`, so the count is at most
`p + (n² − p)/⌊n²/√D⌋`, and the second term can exceed `√D` slightly.  The printed bound is still
true, because the count is an integer, `D` is an integer and `D ≤ n` (`sq_lt_mul_queryCap_add`). -/
theorem totalChunks_le (hD : 16 ≤ D) (hDn : D ≤ n) (hp : p ∈ primesInRange D) :
    (T.totalChunks D p : ℝ) ≤ (p : ℝ) + Real.sqrt D ∧
    (p : ℝ) + Real.sqrt D ≤ 2 * Real.sqrt D := by
  obtain ⟨hprime, hge, hlt⟩ := mem_primesInRange.mp hp
  have hnat : (T.totalChunks D p : ℝ) ≤ (p : ℝ) + (sOf D : ℝ) := by
    exact_mod_cast T.totalChunks_le_add_sOf hD hDn hprime.ne_zero hge
  exact ⟨by linarith [sOf_le_sqrt D], by linarith⟩

/-! ### The instances -/













































































/-- Proof of Theorem 17: "There are at most 2√D h ≤ 2√D(ng/s + 1) ≤ 4ng instances". -/
theorem card_instanceIndices_le (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (hp : p ∈ primesInRange D) :
    ((T.instanceIndices D g p).card : ℝ) ≤ 4 * (n : ℝ) * (g : ℝ) := by
  obtain ⟨hs, hsqrt⟩ := le_sOf_and_sqrt_le hD hDn
  obtain ⟨hchunks, hchunks'⟩ := T.totalChunks_le hD hDn hp
  have hs0 := sOf_pos hD
  have hpieces : (numPieces n D g : ℝ) ≤ (n : ℝ) * (g : ℝ) / (sOf D : ℝ) + 1 :=
    calc (numPieces n D g : ℝ) ≤ (⌈(n : ℝ) * (g : ℝ) / (sOf D : ℝ)⌉₊ : ℝ) := by
          exact_mod_cast numPieces_le hD hg1
      _ ≤ (n : ℝ) * (g : ℝ) / (sOf D : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  -- `2√D · ng/s ≤ 8ng/3` because `s ≥ 3√D/4`, and `2√D ≤ 4n/3 ≤ 4ng/3`.
  have hmain :
      Real.sqrt D * ((n : ℝ) * (g : ℝ) / (sOf D : ℝ)) ≤ 4 / 3 * ((n : ℝ) * (g : ℝ)) := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    calc Real.sqrt D * ((n : ℝ) * (g : ℝ))
        = 4 / 3 * ((n : ℝ) * (g : ℝ)) * (3 * Real.sqrt D / 4) := by ring
      _ ≤ 4 / 3 * ((n : ℝ) * (g : ℝ)) * (sOf D : ℝ) := by gcongr
  have hng : (n : ℝ) ≤ (n : ℝ) * (g : ℝ) :=
    le_mul_of_one_le_right (Nat.cast_nonneg n) (by exact_mod_cast hg1)
  calc ((T.instanceIndices D g p).card : ℝ)
      = (T.totalChunks D p : ℝ) * (numPieces n D g : ℝ) := by
        rw [card_instanceIndices, Nat.cast_mul]
    _ ≤ 2 * Real.sqrt D * (numPieces n D g : ℝ) := by gcongr; exact hchunks.trans hchunks'
    _ ≤ 2 * Real.sqrt D * ((n : ℝ) * (g : ℝ) / (sOf D : ℝ) + 1) := by gcongr
    _ ≤ 4 * (n : ℝ) * (g : ℝ) := by linarith [hmain, hng, hsqrt]

end TriangleInstance

/-! ### The neighborhoods in an instance -/






































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










/-- `queryCapNat n D` is `⌊n²/√D⌋`: both are the greatest `c` with `c² D ≤ n⁴`. -/
theorem queryCapNat_eq (n : ℕ) {D : ℕ} (hD : 1 ≤ D) : queryCapNat n D = queryCap n D := by
  refine (eq_of_forall_le_iff fun c => ?_).symm
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr (Nat.cast_pos.2 hD)
  rw [queryCap, Nat.le_floor_iff (by positivity), le_div_iff₀ hs, queryCapNat, Nat.le_sqrt',
    Nat.le_div_iff_mul_le hD, ← sq_le_sq₀ (by positivity) (by positivity), mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg D), ← pow_mul]
  exact_mod_cast Iff.rfl






















/-- `s = ⌊√D⌋` is the integer square root. -/
theorem sOf_eq_sqrt (D : ℕ) : sOf D = Nat.sqrt D := Real.nat_floor_real_sqrt_eq_nat_sqrt

/-- `pieceSizeNat D g` is the number `⌈s/g⌉` of vertices of a piece, where `s = ⌊√D⌋`. -/
theorem pieceSizeNat_eq (D : ℕ) {g : ℕ} (hg : 1 ≤ g) : pieceSizeNat D g = pieceSize D g := by
  rw [pieceSize, Nat.ceil_div_eq_ceilDiv _ hg, sOf_eq_sqrt]
  rfl

/-- `numPiecesNat n D g` is the number of pieces. -/
theorem numPiecesNat_eq (n D : ℕ) {g : ℕ} (hg : 1 ≤ g) (h : 1 ≤ pieceSize D g) :
    numPiecesNat n D g = numPieces n D g := by
  rw [numPiecesNat, pieceSizeNat_eq D hg, numPieces, Nat.ceil_div_eq_ceilDiv _ h]

/-- The number of chunks of a set of pairs in integer arithmetic. -/
theorem numChunks_eq {n : ℕ} (S : Finset (Fin n × Fin n)) {cap : ℕ} (hcap : 1 ≤ cap) :
    numChunks S cap = S.card ⌈/⌉ cap := by
  rw [numChunks, Nat.ceil_div_eq_ceilDiv _ hcap]

/-- A piece has at least one vertex, and the middle part `C_k × ℤ_p` of an instance has at most `D`
vertices. -/
theorem pieceSize_mul_le {D g p : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g) (hp : p ∈ primesInRange D) :
    1 ≤ pieceSize D g ∧ pieceSize D g * p ≤ D := by
  rw [primesInRange_eq, List.mem_toFinset] at hp
  have hs : 4 ≤ Nat.sqrt D := Nat.le_sqrt'.2 (by omega)
  rw [← pieceSizeNat_eq D hg]
  refine ⟨(Nat.lt_ceilDiv_iff hg).2 (by omega), ?_⟩
  calc pieceSizeNat D g * p ≤ Nat.sqrt D * Nat.sqrt D :=
        Nat.mul_le_mul ((Nat.ceilDiv_le_iff hg).2 (Nat.le_mul_of_pos_right _ hg))
          (le_sqrt_of_mem_primesList hp)
    _ ≤ D := Nat.sqrt_le D

end ThreeSumApsp.Spec

end
end

section


/-!
# The number of chunks, on lists and on sets of pairs (proof of Theorem 17)

The routines work with lists of places: `classIdx` lists the places `a n + b` of the pairs of a
class, and the table `chunkTab` has one entry for each chunk.  The paper's class `W_ϱ` is a set of
pairs (`residueClass`).  The map `(a, b) ↦ a n + b` is a bijection between the set and the list, so
both have the same number of elements (`length_classIdx_eq_card`), and the table has as many entries
as there are chunks "in all" (`length_chunkTab_eq_totalChunks`).  The instance is
`triOf n AB BC AC`, whose weights `w(a,b)` are read from the list `AB`, row by row.
-/

public section

namespace ThreeSumApsp.Spec

variable (n : ℕ) {p : ℕ} (AB BC AC : List ℤ)




















/-- The table has one entry for each chunk. -/
theorem length_chunkTab_eq_totalChunks (hp : p ≠ 0) {D : ℕ} (hD : 1 ≤ D)
    (hcap : 1 ≤ queryCapNat n D) :
    (chunkTab n p (queryCapNat n D) (residList p AB)).length =
      (triOf n AB BC AC).totalChunks D p := by
  rw [length_chunkTab, List.sum_map_range, Finset.sum_range, TriangleInstance.totalChunks]
  refine Finset.sum_congr rfl fun ϱ _ => ?_
  rw [← queryCapNat_eq n hD, numChunks_eq _ hcap, ← length_classIdx_eq_card n AB BC AC hp ϱ]

end ThreeSumApsp.Spec

end
end

section


/-!
# The number of instances of the host of Theorem 17

Proof of Theorem 17: "There are at most 2√D h ≤ 2√D(ng/s + 1) ≤ 4ng instances", where `s = ⌊√D⌋` and
`h` is the number of pieces.  The host's table of chunks has as many entries as the paper's count of
the chunks (`length_chunkTab_eq_totalChunks`), and its number of pieces is the paper's
(`numPiecesNat_eq`), so the bound of `TriangleInstance.card_instanceIndices_le` applies.
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- Proof of Theorem 17: "There are at most 2√D h ≤ 2√D(ng/s + 1) ≤ 4ng instances".  Here `m` is the
number of instances of the host. -/
theorem HostData.m_le {n D g p : ℕ} {AB BC AC : List ℤ} (h : BigCase n D g)
    (hp : p ∈ primesInRange D) :
    (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).m ≤ 4 * n * g := by
  obtain ⟨hD, hDn, hg, -⟩ := h
  have hD1 : 1 ≤ D := by omega
  have hcap : 1 ≤ queryCapNat n D := by rw [queryCapNat_eq n hD1]; exact one_le_queryCap hD1 hDn
  -- The host's numbers of pieces and of chunks are the paper's.
  have hpieces :
      (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).h = numPieces n D g :=
    numPiecesNat_eq n D hg (pieceSize_pos hD hg)
  have hchunks : (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).chunkCount
      = (triOf n AB BC AC).totalChunks D p :=
    length_chunkTab_eq_totalChunks n AB BC AC (mem_primesInRange.mp hp).1.ne_zero hD1 hcap
  have hcard : (((triOf n AB BC AC).instanceIndices D g p).card : ℝ) ≤ ((4 * n * g : ℕ) : ℝ) := by
    push_cast
    exact (triOf n AB BC AC).card_instanceIndices_le hD hDn hg hp
  rw [HostData.m, hpieces, hchunks, Nat.mul_comm, ← TriangleInstance.card_instanceIndices]
  exact_mod_cast hcard

end Light.Sec3

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




















/-! ## False positives, in terms of a bound on the weights -/




/-- The exponent is at least 1. -/
theorem one_le_kappaOf (n U : ℕ) : 1 ≤ kappaOf n U := le_max_left _ _

/-- `U ≤ n^κ` for this exponent. -/
theorem le_rpow_kappaOf {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) :
    (U : ℝ) ≤ (n : ℝ) ^ kappaOf n U := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hU0 : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  calc (U : ℝ) = (n : ℝ) ^ Real.logb n U := (Real.rpow_logb (by linarith) hn1.ne' hU0).symm
    _ ≤ (n : ℝ) ^ kappaOf n U := Real.rpow_le_rpow_of_exponent_le hn1.le (le_max_right _ _)










/-- Weights of absolute value at most `U` are at most `n^κ`. -/
theorem weightsPolyBounded_kappaOf {n U : ℕ} (hn : 2 ≤ n) (hU : 1 ≤ U) {AB BC AC : List ℤ}
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :
    (triOf n AB BC AC).WeightsPolyBounded (kappaOf n U) := by
  have key : ∀ l : List ℤ, AbsLe l U → ∀ i,
      ((|l.getD i 0| : ℤ) : ℝ) ≤ (n : ℝ) ^ kappaOf n U := fun l hl i =>
    le_trans (by exact_mod_cast AbsLe.abs_getD_le (Int.natCast_nonneg U) hl i)
      (le_rpow_kappaOf hn hU)
  exact ⟨fun a b => key AB hAB _, fun b c => key BC hBC _, fun a c => key AC hAC _⟩

/-- **The number of false positives of the chosen prime** (proof of Theorem 17:
"F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)"), with the constant `Hashing.falsePositiveConst`. -/
theorem F_chosenPrime_le {n D U : ℕ} (hD : 16 ≤ D) (hDn : D ≤ n) (hU : 1 ≤ U) {AB BC AC : List ℤ}
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :
    ((triOf n AB BC AC).F (chosenPrime n D AB BC AC) : ℝ) ≤
      Hashing.falsePositiveConst * (kappaOf n U * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) :=
  Hashing.F_le_falsePositiveConst_mul hD hDn (one_le_kappaOf n U) _
    (weightsPolyBounded_kappaOf (by omega) hU hAB hBC hAC) (chosenPrime_isSelected AB BC AC hD)

end ThreeSumApsp.Spec

end
end

section


/-!
# The host of Theorem 17: what is true of the list of its instances

Proof of Theorem 17.  A `HostData` describes the instances that the host forms after the prime has
been chosen, the answers of the solver, and the scans.  This file proves, without any program in
sight:

* the instances are well formed: pieces, chunks, query pairs and matrices have the sizes that the
  solver asks for (`Valid.piece_le`, `Valid.lo_add_le`, `Valid.length_WI`, `length_matX`, …);
* the query pair number `i` of instance `t` is `(rowOf t i, colOf t i)`, read off its place
  `a n + b` (`getD_WI`, `getD_WJ`), which is the entry at position `lo t + i` of the list of all
  pairs; every pair meets every vertex of `C` in some instance (`Valid.exists_query`);
* a query pair `(a, b)` is accepted if and only if the piece has a vertex `c` with `p ∣ S(a,b,c)`,
  where `S(a,b,c) = w(a,b) + w(b,c) + w(a,c)` is `sumAt` (`acc_iff`), and its scan succeeds if and
  only if the piece has a `c` with `S(a,b,c) = 0` (`hit_iff`);
* a zero triangle is found if and only if there is one (`found_m`; for the reduction on finite sets,
  of which `theorem_17` speaks, the same sentence is `TriangleInstance.exists_mem_acceptedPairs`,
  and neither proof uses the other);
* all scans but one fail (`sum_execs_le`);
* the parameters of Theorem 17 give valid data (`valid_of_params`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace HostData













variable {X : HostData}

/-! ## Residues, pieces and chunks -/

/-- The prime is not 0. -/
theorem Valid.p_ne (hv : X.Valid) : X.p ≠ 0 := Nat.ne_of_gt hv.p_pos

/-- All residues are below `p`. -/
theorem Valid.rab_lt (hv : X.Valid) (i : ℕ) : X.RAB.getD i 0 < X.p := by
  rw [RAB, getD_residList]
  exact resid_lt hv.p_ne _

/-- The list of all pairs has `n²` entries. -/
theorem Valid.length_sortedIdx (hv : X.Valid) : (sortedIdx X.n X.p X.RAB).length = X.n * X.n := by
  rw [length_sortedIdx_eq, classStart_eq_sq fun i _ => hv.rab_lt i]

/-- The number `t / chunkCount` of the piece of an instance `t < m` is below the number of pieces.
-/
theorem div_chunkCount_lt {t : ℕ} (ht : t < X.m) : t / X.chunkCount < X.h :=
  Nat.div_lt_of_lt_mul' ht

/-- The number `t % chunkCount` of the chunk of an instance `t < m` is below the number of chunks.
-/
theorem mod_chunkCount_lt {t : ℕ} (ht : t < X.m) : t % X.chunkCount < X.chunkCount :=
  Nat.mod_lt_of_lt_mul ht

/-- The chunk of an instance is an entry of the table of the chunks. -/
theorem chunk_mem {t : ℕ} (ht : t < X.m) : X.chunk t ∈ chunkTab X.n X.p X.cap X.RAB := by
  rw [chunk, List.getD_eq_getElem _ _ (mod_chunkCount_lt ht)]
  exact List.getElem_mem _

/-- The residue of a chunk is below `p`; a chunk has between 1 and `cap` pairs, and it ends within
the list of all pairs. -/
theorem Valid.chunk_entry (hv : X.Valid) {t : ℕ} (ht : t < X.m) :
    (X.chunk t).Fits X.n X.p X.cap :=
  chunkTab_entry hv.cap_pos (fun i _ => hv.rab_lt i) (chunk_mem ht)





/-- A chunk has at most `cap` pairs. -/
theorem w_le_cap (X : HostData) {t : ℕ} (ht : t < X.m) : X.w t ≤ X.cap := by
  obtain ⟨rho, -, i, -, h⟩ := (mem_chunkTab _).1 (chunk_mem ht)
  rw [w, h]
  exact Nat.min_le_left _ _

/-- A chunk ends within the list of all pairs. -/
theorem Valid.lo_add_le (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.lo t + X.w t ≤ X.n * X.n :=
  (hv.chunk_entry ht).end_le

/-- A piece starts below `n`. -/
theorem Valid.c0_lt (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.c0 t < X.n :=
  (Nat.lt_ceilDiv_iff hv.q_pos).1 (div_chunkCount_lt ht)

/-- A piece has at most `q` vertices. -/
theorem len_le (X : HostData) (t : ℕ) : X.len t ≤ X.q := Nat.min_le_left _ _

/-- A piece ends within `C`. -/
theorem Valid.piece_le (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.c0 t + X.len t ≤ X.n := by
  have := hv.c0_lt ht
  rw [len]
  omega

/-- A piece with its labels fits into the middle part. -/
theorem Valid.len_mul_le (hv : X.Valid) (t : ℕ) : X.len t * X.p ≤ X.D :=
  (Nat.mul_le_mul_right _ (X.len_le t)).trans hv.qp_le

/-! ## The query pairs of an instance -/











/-- The rows of the query pairs, as the host lists them. -/
theorem getD_WI {t i : ℕ} (hi : i < X.w t) : (X.WI t).getD i 0 = X.rowOf t i := by
  rw [WI, List.getD_take_of_lt _ hi, List.getD_drop, QI, queryRows, rowOf, place]
  simpa using List.getD_map (l := sortedIdx X.n X.p X.RAB) (d := 0) (n := X.lo t + i) (· / X.n)

/-- The columns of the query pairs, as the host lists them. -/
theorem getD_WJ {t i : ℕ} (hi : i < X.w t) : (X.WJ t).getD i 0 = X.colOf t i := by
  rw [WJ, List.getD_take_of_lt _ hi, List.getD_drop, QJ, queryCols, colOf, place]
  simpa using List.getD_map (l := sortedIdx X.n X.p X.RAB) (d := 0) (n := X.lo t + i) (· % X.n)

/-- A place is below `n²`. -/
theorem Valid.place_lt (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.place t i < X.n * X.n := by
  have hend := hv.lo_add_le ht
  have hlen := hv.length_sortedIdx
  rw [place, List.getD_eq_getElem _ _ (by omega)]
  exact lt_of_mem_sortedIdx (List.getElem_mem _)

/-- The row of a query pair is a vertex of `A`. -/
theorem Valid.rowOf_lt (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.rowOf t i < X.n := Nat.div_lt_of_lt_mul' (hv.place_lt ht hi)

/-- The column of a query pair is a vertex of `B`. -/
theorem Valid.colOf_lt (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.colOf t i < X.n := Nat.mod_lt_of_lt_mul (hv.place_lt ht hi)

/-- The pair gives the place back. -/
theorem rowOf_mul_add_colOf (X : HostData) (t i : ℕ) :
    X.rowOf t i * X.n + X.colOf t i = X.place t i := Nat.div_add_mod' _ _

/-- The weight `w(a,b)` of a query pair has the residue of its chunk. -/
theorem Valid.rab_place (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.RAB.getD (X.place t i) 0 = X.rho t := chunkTab_class hv.cap_pos (chunk_mem ht) hi


























/-- The list of the rows of all pairs has `n²` entries. -/
theorem Valid.length_QI (hv : X.Valid) : X.QI.length = X.n * X.n := by
  rw [QI, queryRows, List.length_map, hv.length_sortedIdx]

/-- The list of the columns of all pairs has `n²` entries. -/
theorem Valid.length_QJ (hv : X.Valid) : X.QJ.length = X.n * X.n := by
  rw [QJ, queryCols, List.length_map, hv.length_sortedIdx]

/-- An instance lists the row of each of its query pairs. -/
theorem Valid.length_WI (hv : X.Valid) {t : ℕ} (ht : t < X.m) : (X.WI t).length = X.w t := by
  have := hv.lo_add_le ht
  rw [WI, List.length_take, List.length_drop, hv.length_QI]
  omega

/-- An instance lists the column of each of its query pairs. -/
theorem Valid.length_WJ (hv : X.Valid) {t : ℕ} (ht : t < X.m) : (X.WJ t).length = X.w t := by
  have := hv.lo_add_le ht
  rw [WJ, List.length_take, List.length_drop, hv.length_QJ]
  omega

/-! ## The two matrices of an instance -/



















/-- Every place stands at some position of the list of all pairs. -/
theorem Valid.exists_getD_sortedIdx (hv : X.Valid) {s : ℕ} (hs : s < X.n * X.n) :
    ∃ j < X.n * X.n, (sortedIdx X.n X.p X.RAB).getD j 0 = s := by
  have hmem : s ∈ sortedIdx X.n X.p X.RAB :=
    List.mem_flatMap.2 ⟨X.RAB.getD s 0, List.mem_range.2 (hv.rab_lt s), mem_classIdx.2 ⟨hs, rfl⟩⟩
  obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hmem
  exact ⟨j, hv.length_sortedIdx ▸ hj, (List.getD_eq_getElem _ _ hj).trans hjs⟩

/-- Proof of Theorem 17, "its c lies in some piece": every pair `(a, b)` is a query pair of an
instance whose piece contains a given vertex `c`. -/
theorem Valid.exists_query (hv : X.Valid) {a b c : ℕ} (ha : a < X.n) (hb : b < X.n)
    (hc : c < X.n) :
    ∃ t < X.m, ∃ i < X.w t,
      X.rowOf t i = a ∧ X.colOf t i = b ∧ ∃ c' < X.len t, X.c0 t + c' = c := by
  -- The position `j` of the pair in the list of all pairs, and the chunk `k` of that position.
  obtain ⟨j, hj, hplace⟩ := hv.exists_getD_sortedIdx (Nat.mul_add_lt_mul ha hb)
  obtain ⟨y, hy, hlo, hhi⟩ := chunkTab_cover hv.cap_pos (fun i _ => hv.rab_lt i) hj
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  -- The instance of that chunk and of the piece of `c`.
  have hpiece : c / X.q < X.h :=
    (Nat.lt_ceilDiv_iff hv.q_pos).2 (lt_of_le_of_lt (Nat.div_mul_le_self c X.q) hc)
  obtain ⟨t, ht, hdiv, hmod⟩ : ∃ t < X.m, t / X.chunkCount = c / X.q ∧ t % X.chunkCount = k :=
    ⟨_, Nat.mul_add_lt_mul hpiece hk, Nat.mul_add_div_of_lt hk, Nat.mul_add_mod_of_lt hk⟩
  have hentry : X.chunk t = (chunkTab X.n X.p X.cap X.RAB)[k] := by
    rw [chunk, hmod]
    exact List.getD_eq_getElem _ _ hk
  have hlo' : X.lo t ≤ j := by rw [lo, hentry]; exact hlo
  have hhi' : j < X.lo t + X.w t := by rw [lo, w, hentry]; exact hhi
  have hpair : X.place t (j - X.lo t) = a * X.n + b := by
    rw [place, Nat.add_sub_cancel' hlo', hplace]
  have hdivmod := Nat.div_add_mod' c X.q
  refine ⟨t, ht, j - X.lo t, by omega, ?_, ?_, c % X.q, ?_, ?_⟩
  · rw [rowOf, hpair, Nat.mul_add_div_of_lt hb]
  · rw [colOf, hpair, Nat.mul_add_mod_of_lt hb]
  · have := Nat.mod_lt c hv.q_pos
    rw [len, c0, hdiv]
    omega
  · rw [c0, hdiv, hdivmod]

/-! ## Acceptance -/






/-- A sum of numbers that are 0 or 1 is not 0 if and only if one of them is 1. -/
private theorem sum_ne_zero_iff (f : ℕ → ℤ) (N : ℕ) (h01 : ∀ k < N, f k = 0 ∨ f k = 1) :
    ((List.range N).map f).sum ≠ 0 ↔ ∃ k < N, f k = 1 := by
  have hnonneg : ∀ k ∈ Finset.range N, 0 ≤ f k := fun k hk => by
    rcases h01 k (Finset.mem_range.1 hk) with h | h <;> omega
  rw [List.sum_map_range, Ne, Finset.sum_eq_zero_iff_of_nonneg hnonneg]
  constructor
  · intro hne
    by_contra hnone
    exact hne fun k hk => (h01 k (Finset.mem_range.1 hk)).resolve_right
      fun hone => hnone ⟨k, Finset.mem_range.1 hk, hone⟩
  · rintro ⟨k, hk, hone⟩ hall
    have := hall k (Finset.mem_range.2 hk)
    omega

/-- Proof of Theorem 17: "the condition S(a,b,c) ≡ 0 (mod p) has become the equality w(a,c) + ϱ ≡
−w(b,c) of a label of (a,c) and a label of (b,c)".  Here `wAC`, `wAB` and `wBC` are the three
weights, and `ϱ` is the residue of `wAB`. -/
private theorem labels_eq_iff {p : ℕ} (hp : p ≠ 0) (wAC wAB wBC : ℤ) :
    (resid p wAC + resid p wAB) % p = (p - resid p wBC) % p ↔ (p : ℤ) ∣ wAB + wBC + wAC := by
  have hleft : ((resid p wAC + resid p wAB : ℕ) : ℤ) ≡ wAC + wAB [ZMOD (p : ℤ)] := by
    push_cast
    rw [resid_cast hp, resid_cast hp]
    exact (Int.mod_modEq wAC p).add (Int.mod_modEq wAB p)
  have hright : ((p - resid p wBC : ℕ) : ℤ) ≡ -wBC [ZMOD (p : ℤ)] := by
    rw [Nat.cast_sub (resid_lt hp wBC).le, resid_cast hp]
    simpa using (Int.modEq_zero_iff_dvd.2 (dvd_refl (p : ℤ))).sub (Int.mod_modEq wBC p)
  have hiff : wAC + wAB ≡ -wBC [ZMOD (p : ℤ)] ↔ (p : ℤ) ∣ wAB + wBC + wAC := by
    rw [Int.modEq_iff_dvd, ← dvd_neg, show -(-wBC - (wAC + wAB)) = wAB + wBC + wAC by ring]
  rw [← hiff, ← Nat.ModEq, ← Int.natCast_modEq_iff]
  exact ⟨fun h => (hleft.symm.trans h).trans hright, fun h => (hleft.trans h).trans hright.symm⟩

/-- An entry of the matrix `X` of an instance. -/
private theorem getD_xList {n D p c0 len rho : ℕ} {RAC : List ℕ} {a k : ℕ} (ha : a < n)
    (hk : k < D) :
    (xList n D p c0 len rho RAC).getD (a * D + k) 0 =
      if k / p < len ∧ k % p = (RAC.getD (a * n + c0 + k / p) 0 + rho) % p then 1 else 0 := by
  rw [xList, List.getD_map_range _ (Nat.mul_add_lt_mul ha hk), Nat.mul_add_mod_of_lt hk,
    Nat.mul_add_div_of_lt hk]

/-- An entry of the matrix `Y` of an instance. -/
private theorem getD_yList {n D p c0 len : ℕ} {RBC : List ℕ} {b k : ℕ} (hb : b < n) (hk : k < D) :
    (yList n D p c0 len RBC).getD (k * n + b) 0 =
      if k / p < len ∧ k % p = (p - RBC.getD (b * n + c0 + k / p) 0) % p then 1 else 0 := by
  rw [yList, List.getD_map_range _ (Nat.mul_add_lt_mul hk hb), Nat.mul_add_mod_of_lt hb,
    Nat.mul_add_div_of_lt hb]

/-- The entry `(XY)[a, b]` of an instance is not 0 if and only if the labels of `a` and `b` agree at
some vertex of the piece. -/
private theorem thinEntry_ne_zero_iff {n D p c0 len rho : ℕ} {RAC RBC : List ℕ} {a b : ℕ}
    (hp : p ≠ 0) (hlen : len * p ≤ D) (ha : a < n) (hb : b < n) :
    thinEntry n D (xList n D p c0 len rho RAC) (yList n D p c0 len RBC) a b ≠ 0 ↔
      ∃ c < len,
        (RAC.getD (a * n + c0 + c) 0 + rho) % p = (p - RBC.getD (b * n + c0 + c) 0) % p := by
  rw [thinEntry, sum_ne_zero_iff]
  · constructor
    · -- The column `k` is the middle vertex `(c, σ)` with `c = k / p` and `σ = k % p`.
      rintro ⟨k, hk, hone⟩
      rw [getD_xList ha hk, getD_yList hb hk] at hone
      split_ifs at hone with hX hY
      · exact ⟨k / p, hX.1, hX.2.symm.trans hY.2⟩
      all_goals simp at hone
    · -- The middle vertex `(c, σ)` with the common label `σ` is the column `c p + σ`.
      rintro ⟨c, hc, hlabel⟩
      have hσ : (RAC.getD (a * n + c0 + c) 0 + rho) % p < p := Nat.mod_lt _ (Nat.pos_of_ne_zero hp)
      have hk := (Nat.mul_add_lt_mul hc hσ).trans_le hlen
      refine ⟨_, hk, ?_⟩
      rw [getD_xList ha hk, getD_yList hb hk, Nat.mul_add_div_of_lt hσ, Nat.mul_add_mod_of_lt hσ,
        if_pos ⟨hc, rfl⟩, if_pos ⟨hc, hlabel⟩, mul_one]
  · intro k hk
    rw [getD_xList ha hk, getD_yList hb hk]
    split_ifs <;> simp

/-- The answer of the solver for a query pair: 1 if `(XY)[a, b] ≠ 0`, and 0 otherwise. -/
theorem Valid.getD_ans (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    (X.ans t).getD i 0 =
      if thinEntry X.n X.D (X.matX t) (X.matY t) (X.rowOf t i) (X.colOf t i) = 0 then 0 else 1 := by
  have hiI : i < (X.WI t).length := by rw [hv.length_WI ht]; exact hi
  have hiJ : i < (X.WJ t).length := by rw [hv.length_WJ ht]; exact hi
  have hzip : i < ((X.WI t).zip (X.WJ t)).length := by rw [List.length_zip]; omega
  rw [← getD_WI hi, ← getD_WJ hi, ans, thinOut, List.getD_eq_getElem _ _ (by simpa using hzip),
    List.getElem_map, List.getElem_map, List.getElem_zip, List.getD_eq_getElem _ _ hiI,
    List.getD_eq_getElem _ _ hiJ]

/-- Proof of Theorem 17: "a query pair (a,b) ∈ 𝒬 has a common neighbor if and only if some c ∈ C_k
has S(a,b,c) ≡ 0 (mod p)". -/
theorem acc_iff (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.acc t i = true ↔
      ∃ c < X.len t, (X.p : ℤ) ∣ X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) := by
  have hentry : X.acc t i = true ↔
      thinEntry X.n X.D (X.matX t) (X.matY t) (X.rowOf t i) (X.colOf t i) ≠ 0 := by
    rw [acc, decide_eq_true_eq, hv.getD_ans ht hi]
    split_ifs with h <;> simp [h]
  rw [hentry, matX, matY, thinEntry_ne_zero_iff hv.p_ne (hv.len_mul_le t) (hv.rowOf_lt ht hi)
    (hv.colOf_lt ht hi)]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [RAC, RBC, getD_residList, getD_residList, ← hv.rab_place ht hi, RAB, getD_residList,
    labels_eq_iff hv.p_ne, ← rowOf_mul_add_colOf, sumAt, Nat.add_assoc, Nat.add_assoc]

/-- Proof of Theorem 17, "scan the piece C_k of its instance for a c with S(a,b,c) = 0": when the
scan succeeds.
-/
theorem hit_iff {t i : ℕ} (hi : i < X.w t) :
    X.hit t i = true ↔ ∃ c < X.len t, X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) = 0 := by
  rw [hit, getD_WI hi, getD_WJ hi]
  simp [scanHit, sumAt, Nat.add_assoc]

/-! ## Correctness -/

/-- Brute force finds a zero triangle if and only if there is one. -/
private theorem hasZero_iff_sumAt (X : HostData) :
    hasZero X.n X.AB X.BC X.AC = true ↔ ∃ a < X.n, ∃ b < X.n, ∃ c < X.n, X.sumAt a b c = 0 := by
  simp [hasZero, scanHit, sumAt]

/-- A zero triangle has been found before instance `T` if and only if some accepted query pair of an
earlier instance has a successful scan. -/
theorem found_iff (X : HostData) (T : ℕ) :
    X.found T = true ↔ ∃ t < T, ∃ i < X.w t, X.acc t i = true ∧ X.hit t i = true := by
  induction T with
  | zero => simp [found]
  | succ T ih =>
    rw [found, foundAt, Bool.or_eq_true, ih, List.any_eq_true]
    constructor
    · rintro (⟨t, ht, h⟩ | ⟨i, hi, h⟩)
      · exact ⟨t, by omega, h⟩
      · exact ⟨T, by omega, i, List.mem_range.1 hi, Bool.and_eq_true _ _ ▸ h⟩
    · rintro ⟨t, ht, i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with hlt | rfl
      · exact Or.inl ⟨t, hlt, i, hi, h⟩
      · exact Or.inr ⟨i, List.mem_range.2 hi, by rw [Bool.and_eq_true]; exact h⟩

/-- Proof of Theorem 17: "A zero triangle is always found, since its c lies in some piece and makes
the oracle accept its pair."  After all instances a zero triangle has been found if and only if
there is one.
-/
theorem found_m (hv : X.Valid) : X.found X.m = hasZero X.n X.AB X.BC X.AC := by
  rw [Bool.eq_iff_iff, found_iff, hasZero_iff_sumAt]
  constructor
  · rintro ⟨t, ht, i, hi, -, hhit⟩
    obtain ⟨c, hc, hzero⟩ := (hit_iff hi).1 hhit
    have hpiece := hv.piece_le ht
    exact ⟨_, hv.rowOf_lt ht hi, _, hv.colOf_lt ht hi, _, by omega, hzero⟩
  · rintro ⟨a, ha, b, hb, c, hc, hzero⟩
    obtain ⟨t, ht, i, hi, rfl, rfl, c', hc', rfl⟩ := hv.exists_query ha hb hc
    exact ⟨t, ht, i, hi, (acc_iff hv ht hi).2 ⟨c', hc', hzero ▸ dvd_zero _⟩,
      (hit_iff hi).2 ⟨c', hc', hzero⟩⟩

/-- Proof of Theorem 17: "We stop as soon as a zero triangle is found", so all scans but one fail.
-/
theorem sum_execs_le (X : HostData) :
    ∑ t ∈ Finset.range X.m, X.execs t ≤ ∑ t ∈ Finset.range X.m, X.fails t + 1 := by
  have key : ∀ T, ∑ t ∈ Finset.range T, X.execs t
      ≤ ∑ t ∈ Finset.range T, X.fails t + (X.found T).toNat := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      have hstep : X.execs T + (X.found T).toNat ≤ X.fails T + (X.found (T + 1)).toNat :=
        execsUpto_le (X.acc T) (X.hit T) (X.found T) (X.w T)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega
  have hone : (X.found X.m).toNat ≤ 1 := Bool.toNat_le _
  have := key X.m
  omega

/-- The parameters of Theorem 17 give valid data. -/
theorem valid_of_params {n D g p : ℕ} {AB BC AC : List ℤ} (h : BigCase n D g)
    (hp : p ∈ primesInRange D) (lenAB : AB.length = n * n) (lenBC : BC.length = n * n)
    (lenAC : AC.length = n * n) :
    (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).Valid where
  n_pos := le_trans (by norm_num) (h.sixteen_le.trans h.le_n)
  p_pos := (mem_primesInRange.mp hp).1.one_le
  q_pos := by
    simp only
    rw [pieceSizeNat_eq D h.one_le_g]
    exact (pieceSize_mul_le h.sixteen_le h.one_le_g hp).1
  cap_pos := by
    have hD := h.sixteen_le
    have hDn := h.le_n
    simp only
    rw [queryCapNat, Nat.le_sqrt, Nat.le_div_iff_mul_le (by omega)]
    have : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
    omega
  qp_le := by
    simp only
    rw [pieceSizeNat_eq D h.one_le_g]
    exact (pieceSize_mul_le h.sixteen_le h.one_le_g hp).2
  lenAB := lenAB
  lenBC := lenBC
  lenAC := lenAC

end HostData

end Light.Sec3

end
end

section


/-!
# Brute force (the proof of Theorem 19)

In the proof of Theorem 19, "smaller instances are solved by brute force": the procedure brute
(`bruteBody`) scans all of `C` for every pair `(a, b)` (`brute_spec`, `brute_meets`).  It takes at
most `100 n³ + 100` steps (`brute_solves`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Brute force finds a zero triangle if and only if there is one. -/
theorem hasZero_iff (n : ℕ) (AB BC AC : List ℤ) :
    hasZero n AB BC AC = true ↔ (triOf n AB BC AC).HasZeroTriangle := by
  unfold hasZero TriangleInstance.HasZeroTriangle TriangleInstance.IsZeroTriangle TriangleInstance.S
  simp only [List.any_eq_true, List.mem_range, scanHit, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, h⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, by simpa [triOf] using h⟩
  · rintro ⟨a, b, c, h⟩
    exact ⟨a, a.2, b, b.2, c, c.2, by simpa [triOf] using h⟩









theorem bruteRow_succ (n : ℕ) (AB BC AC : List ℤ) (a b : ℕ) :
    bruteRow n AB BC AC a (b + 1) = (bruteRow n AB BC AC a b || scanHit n AB BC AC a b 0 n) := by
  simp [bruteRow, List.range_succ, List.any_append]

theorem bruteAll_succ (n : ℕ) (AB BC AC : List ℤ) (a : ℕ) :
    bruteAll n AB BC AC (a + 1) = (bruteAll n AB BC AC a || bruteRow n AB BC AC a n) := by
  simp [bruteAll, List.range_succ, List.any_append]

namespace Brute














end Brute






















/-- An instance of Exact Triangle gives `scan` what it assumes. -/
theorem _root_.Light.TriInst.Pre.weights {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Weights lim μ x.ab x.bc x.ac x.n x.U x.AB x.BC x.AC where
  hw := hok.space
  hU := by exact_mod_cast hok.word
  arrAB := ⟨hpre.lenAB, hpre.segAB, hpre.leAB, hpre.belowAB.trans hok.cells⟩
  arrBC := ⟨hpre.lenBC, hpre.segBC, hpre.leBC, hpre.belowBC.trans hok.cells⟩
  arrAC := ⟨hpre.lenAC, hpre.segAC, hpre.leAC, hpre.belowAC.trans hok.cells⟩

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}

/-- One pair: the result so far takes the scan for `(a, b)` in. -/
theorem brutePair_spec {b : ℕ} {hit : Bool} {r : ℤ} (hP : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (hd : d < lim.depth) (ha : a < n) (hb : b < n) :
    Ends lim P d (brutePair pScan) ⟨frame [n, U, ab, bc, ac, fr, a, b, bit hit, r], μ⟩
      (tScan n + 16) fun σ' => ∃ r', σ' = ⟨frame [n, U, ab, bc, ac, fr, a, b,
        bit (hit || scanHit n AB BC AC a b 0 n), r'], μ⟩ := by
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.arrAB); (obtain ⟨⟩ := id C.arrBC);
    (obtain ⟨⟩ := id C.arrAC))
  -- res := scan(ab, bc, ac, n, a, b, 0, n)
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
            ((scan_meets hP C ha hb (c0 := 0) (Nat.zero_add n).le) _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (scan_meets hP C ha hb (c0 := 0) (Nat.zero_add n).le) ?_ ?_ ?_ ?_);
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
        ((rintro _ _ ⟨rfl, rfl⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [flag_eq_bit]
  -- if res = 1 then hit := 1
  cases hscan : scanHit n AB BC AC a b 0 n
  · exact Ends.iteLast (fun h => absurd h (by simp [bit])) fun _ => Ends.skip ⟨bit false, by simp⟩
  · exact Ends.iteLast (fun _ => Ends.setTo 1 ⟨bit true, by simp [bit]⟩)
      fun h => absurd h (by simp [bit])

/-- The inner loop: all `b` for one `a`. -/
theorem bruteInner_spec {b₀ r₀ : ℤ} (hP : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (hd : d < lim.depth) (hn : n ≤ lim.space)
    (ha : a < n) :
    Ends lim P d (bruteInner pScan)
      ⟨frame [n, U, ab, bc, ac, fr, a, b₀, bit (bruteAll n AB BC AC a), r₀], μ⟩
      (n * (24 * n + 59) + 6) fun σ' => ∃ r, σ' = ⟨frame [n, U, ab, bc, ac, fr, a, n,
        bit (bruteAll n AB BC AC (a + 1)), r], μ⟩ := by
  have hw := C.hw
  -- for b < n
  refine Ends.for (fun b σ => ∃ r, σ = ⟨frame [n, U, ab, bc, ac, fr, a, b,
    bit (bruteAll n AB BC AC a || bruteRow n AB BC AC a b), r], μ⟩) n (tScan n + 16)
    ?start ?round ?done ?bound (hT := by simp [tScan]; ring_nf; omega)
  case start => exact ⟨r₀, by simp [update_frame_setLocal, bruteRow]⟩
  case bound =>
    rintro b _ - - ⟨r, rfl⟩
    simp
  case round =>
    rintro b _ hb - ⟨r, rfl⟩
    refine (brutePair_spec hP C hd ha hb).mono le_rfl ?_
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, r', by simp [update_frame_setLocal, bruteRow_succ, Bool.or_assoc]⟩
  case done =>
    rintro _ - ⟨r, rfl⟩
    exact ⟨r, by rw [bruteAll_succ]⟩

end

/-- The steps of the two loops of brute are within its time. -/
theorem tBrute_ge (n : ℕ) : n * (1 + (n * (24 * n + 59) + 6) + 7) + 10 ≤ tBrute n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tBrute]
  · have hsq : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by omega)
    have hlin : n ≤ n ^ 3 := Nat.le_self_pow (by omega) n
    rw [show n * (1 + (n * (24 * n + 59) + 6) + 7) = 24 * n ^ 3 + 59 * n ^ 2 + 14 * n by ring,
      tBrute]
    omega

/-- **The brute force.**  In any program that holds `scanBody` as its procedure number `pScan`,
`bruteBody pScan` ends within `tBrute n` steps, decides whether the instance has a zero triangle,
and changes no cell. -/
theorem brute_spec {pScan : ℕ} (hP : P[pScan]? = some scanBody) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : x.Pre μ fr) (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Ends lim P d (bruteBody pScan) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ (tBrute x.n)
      fun σ' => σ'.loc 0 = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ σ'.mem = μ := by
  have C := hpre.weights hok
  have hw := C.hw
  have hd : d < lim.depth := hok.depth
  have hn : x.n ≤ lim.space :=
    (Nat.le_mul_of_pos_left _ hpre.n_pos).trans ((Nat.le_add_left _ _).trans C.arrAB.below)
  have htime := tBrute_ge x.n
  -- hit := 0
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
            -- for a < n
            
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
  -- for a < n
  refine Ends.next _ (Ends.for (fun a σ => ∃ b r, σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr, a, b,
    bit (bruteAll x.n x.AB x.BC x.AC a), r], μ⟩) x.n (x.n * (24 * x.n + 59) + 6)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp; omega)
  case start =>
    exact ⟨0, 0, by simpa [update_frame_setLocal, bruteAll, bit] using
      (frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr, 0, 0, 0] 1).symm⟩
  case bound =>
    rintro a _ - - ⟨b, r, rfl⟩
    simp
  case round =>
    rintro a _ ha - ⟨b, r, rfl⟩
    refine (bruteInner_spec hP C hd hn ha).mono le_rfl ?_
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, x.n, r', by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ - ⟨b, r, rfl⟩
    -- return hit
    refine Ends.setTo (bit (hasZero x.n x.AB x.BC x.AC)) ⟨?_, rfl⟩
      (by simp [bruteAll, hasZero, bruteRow]) (by simp; omega)
    exact (flag_eq_bit _).symm.trans (flag_congr (hasZero_iff x.n x.AB x.BC x.AC))

/-- The specification of `brute`, for its callers. -/
theorem brute_meets {p pScan : ℕ} (hB : P[p]? = some (bruteBody pScan))
    (hP : P[pScan]? = some scanBody) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Meets lim P p d [x.n, x.U, x.ab, x.bc, x.ac, fr] μ (tBrute x.n) fun r μ' =>
      r = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ μ' = μ :=
  Meets.of_body hB (brute_spec hP x μ fr hpre hok)






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





/-- There are at most `4ng` instances. -/
theorem hostData_m_le {x : TriInst} {D g : ℕ} (h : BigCase x.n D g) :
    (hostData x D g).m ≤ 4 * x.n * g :=
  HostData.m_le h (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le)

/-- The data of a run are valid. -/
theorem hostData_valid {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) : (hostData x D g).Valid :=
  HostData.valid_of_params h (chosenPrime_mem x.AB x.BC x.AC h.sixteen_le) hpre.lenAB hpre.lenBC
    hpre.lenAC

/-! ## The addresses -/


















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

































































end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the parameters and the small case

The first part of the host procedure `et17` (Exact Triangle by Theorem 17) computes `D`, `g` and
`s = ⌊√D⌋` and tests whether `n` is small (`et17Params_spec`).  If it is, the host calls the brute
force (`et17Small_spec`; proof of Theorem 19: "smaller instances are solved by brute force").
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ} {lim : Limits} {d : ℕ}

/-- **The first part of et17**: the parameters, and whether n is small.  No cell changes. -/
theorem et17Params_spec (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst)
    (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Params ν) ⟨frame (et17Loc0 x fr), μ⟩
      (tD x.n + tG (Dfun x.n) + (18 * Nat.sqrt (Dfun x.n) + 12) + 40)
      fun σ' => σ' = ⟨frame (et17LocA x fr (Dfun x.n) (Gfun (Dfun x.n))), μ⟩ := by
  have hn := hpre.n_pos
  have hDpos := C.D_pos x.n hn
  unfold hostNeed at hok
  have hdepth := hok.depth
  simp only [hostNeedAt] at hdepth
  generalize hD : Dfun x.n = D at *
  generalize hg : Gfun D = g at *
  -- The numbers that this part forms fit in a word.
  have hwD : ((wD x.n : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hwG : ((wG D : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have hsqrt : ((3 * D + 4 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  have h16 : ((16 : ℕ) : ℤ) ≤ lim.word := le_word_of_le_hostWord hok
  unfold et17Params et17Loc0 et17LocA
  -- D := Dfun(n); g := Gfun(D)
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
            ((C.dProc lim d x.n μ hn hok.space hwD (by omega)) _ (by omega)) ?_ ?_
            ?_ ?_
      |
        refine
          Light.Ends.callToThen (C.dProc lim d x.n μ hn hok.space hwD (by omega))
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
        ((rintro _ μ ⟨rfl, rfl⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hD]
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
            ((C.gProc lim d D μ hDpos hok.space hwG (by omega)) _ (by omega)) ?_
            ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (C.gProc lim d D μ hDpos hok.space hwG (by omega))
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
        ((rintro _ μ ⟨rfl, rfl⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hg]
  -- s := sqrt(D)
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
            ((sqrt_meets (K := D) C.hSqrt μ hsqrt) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen (sqrt_meets (K := D) C.hSqrt μ hsqrt) ?_ ?_ ?_
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
        ((rintro _ μ
              ⟨rfl, rfl⟩
                  -- the four tests: D < 16, n < D, g < 1, s < g
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- the four tests: D < 16, n < D, g < 1, s < g
  refine Ends.block ⟨by simp; omega, ?_⟩
  by_cases hD16 : D < 16 <;> by_cases hnD : x.n < D <;> by_cases hg0 : g = 0 <;>
    by_cases hsg : Nat.sqrt D < g <;> simp [update_frame_setLocal, SmallCase, hD16, hnD, hg0, hsg]

open Et17 in
/-- **The small case**: the call of the brute force. -/
theorem et17Small_spec (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG) (x : TriInst)
    (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (.call ν.pBrute [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free] 0)
      ⟨frame (et17LocA x fr D g), μ⟩ (tBrute x.n + 8)
      fun σ' => etTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hbrute : (bruteNeed x.n x.U).Ok lim fr (d + 1) :=
    hok.mono (by simp only [bruteNeed, hostNeedAt, hostWord]; omega)
      (by simp only [bruteNeed]; omega) (by simp only [bruteNeed, hostNeedAt]; omega)
  have hdepth := hok.depth
  simp only [hostNeedAt] at hdepth
  refine Ends.callTo (brute_meets C.hBrute C.loop.scan x μ fr hpre hbrute) ?_ (by simp [et17LocA])
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨by simp [et17LocA], fun _ _ => rfl⟩

end Light.Sec3

end
end

section


/-!
# Theorem 17, third step: witnesses

For every query pair that the oracle accepts, the piece `C_k` of its instance is scanned for a `c`
with `S(a,b,c) = 0`, and the scans stop at the first zero triangle.  As in the paper:

* a zero triangle is always found (`TriangleInstance.exists_mem_acceptedPairs`);
* a failed scan contains a false positive of `p`
  (`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`), and distinct scans contain
  distinct false positives (`TriangleInstance.eq_of_mem_acceptedPairs`), so there are at most `F(p)`
  failed scans (`TriangleInstance.card_le_F_of_distinct_scans`,
  `TriangleInstance.card_failedScans_le`);
* a scan looks at at most `⌈s/g⌉ ≤ 2√D/g` vertices (`pieceSize_le_two_mul_sqrt_div`), so the scans
  cost `O((F(p) + 1)√D/g) = O(κ n³ log n/g)` (`TriangleInstance.F_add_one_mul_pieceSize_le`).

`Theorem17.correctness` puts the first two together.

The program for Theorem 17 works on lists, and for its lists the sentences of this step are lemmas
of their own: `HostData.found_m` answers `TriangleInstance.exists_mem_acceptedPairs`,
`HostData.exists_false_positive` answers
`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`, `HostData.Valid.eq_of_place_eq`
answers `TriangleInstance.eq_of_mem_acceptedPairs`, and `HostData.sum_fails_le` answers
`TriangleInstance.card_failedScans_le`.  The two proofs share `F(p)`, the first step of the
proof, the number of instances and the counting step `TriangleInstance.card_le_F_of_distinct_scans`;
no theorem about programs rests on another lemma of this file.
-/

@[expose] public section

namespace ThreeSumApsp

variable {n D g p : ℕ}

namespace TriangleInstance

variable {T : TriangleInstance ℤ n}

/-! ### Scans and accepted pairs -/
















variable (T) (D g)






































variable (p) (ans : InstanceIndex p → Fin n × Fin n → Bool)











variable {T D g p ans}








/-! ### The sentences of the paragraph "Witnesses" -/














































/-- Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans", for any finite family `s` of scans and any notion "the scan `x` contains the triple
`t`".  The scans of the accepted pairs (`card_failedScans_le`) and the scans of the program
(`HostData.sum_fails_le`) are two such families. -/
theorem card_le_F_of_distinct_scans (T : TriangleInstance ℤ n) {σ : Type*} (s : Finset σ)
    (contains : σ → Fin n × Fin n × Fin n → Prop)
    (hfalse : ∀ x ∈ s, ∃ t, contains x t ∧ T.IsFalsePositive p t)
    (hdistinct : ∀ t, ∀ x ∈ s, ∀ y ∈ s, contains x t → contains y t → x = y) :
    s.card ≤ T.F p := by
  classical
  refine Finset.card_le_card_of_forall_subsingleton contains (fun x hx => ?_)
    fun t _ x hx y hy => hdistinct t x hx.1 y hy.1 hx.2 hy.2
  obtain ⟨t, ht, hfp⟩ := hfalse x hx
  exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfp⟩, ht⟩













end TriangleInstance







































/-! ### The output of the reduction -/


























end ThreeSumApsp

end
end

section


/-!
# The host of Theorem 17: failed scans and false positives

Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans" (`HostData.sum_fails_le`).  An accepted query pair `(a, b)` of an instance whose scan
fails has a vertex `c` in the piece of the instance with `p ∣ S(a,b,c)` and `S(a,b,c) ≠ 0`
(`exists_false_positive`); such a triple is a false positive of `p`, and `F(p)` is their number.
Different pairs (instance, query pair) give different triples (`Valid.eq_of_place_eq`): `c`
determines the piece; `(a, b)` determines the place `a n + b`; the place determines the position in
the list of all pairs, which has no repetition; and the position determines the chunk.

The statement `theorem_17` is about the reduction on finite sets, and there the same sentences are
`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`,
`TriangleInstance.eq_of_mem_acceptedPairs` and `TriangleInstance.card_failedScans_le`.  The two
proofs run in parallel.  They share `F(p)` and the counting step, which is stated for any family of
scans (`TriangleInstance.card_le_F_of_distinct_scans`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace HostData

variable {X : HostData}

/-- Two query pairs at the same place, of instances with the same piece, are the same. -/
theorem Valid.eq_of_place_eq (hv : X.Valid) {t t' i i' : ℕ} (ht : t < X.m) (ht' : t' < X.m)
    (hi : i < X.w t) (hi' : i' < X.w t') (hplace : X.place t i = X.place t' i')
    (hpiece : t / X.chunkCount = t' / X.chunkCount) : t = t' ∧ i = i' := by
  have hlen := hv.length_sortedIdx
  have hend := hv.lo_add_le ht
  have hend' := hv.lo_add_le ht'
  -- The list of all pairs has no repetition, so the two pairs stand at the same position in it.
  have hpos : X.lo t + i = X.lo t' + i' := by
    rw [place, place, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      at hplace
    exact (List.Nodup.getElem_inj_iff (sortedIdx_nodup X.n X.p X.RAB)).1 hplace
  -- A position lies in one chunk only.
  have hchunk : ∀ s (hs : s % X.chunkCount < (chunkTab X.n X.p X.cap X.RAB).length),
      (chunkTab X.n X.p X.cap X.RAB)[s % X.chunkCount] = X.chunk s := fun s hs =>
    (List.getD_eq_getElem _ _ hs).symm
  have hmod : t % X.chunkCount = t' % X.chunkCount :=
    chunkTab_unique hv.cap_pos (j := X.lo t + i) (mod_chunkCount_lt ht) (mod_chunkCount_lt ht')
      (hchunk t _ ▸ ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩)
      (hchunk t' _ ▸ hpos ▸ ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi' _⟩)
  obtain rfl : t = t' := by
    rw [← Nat.div_add_mod t X.chunkCount, ← Nat.div_add_mod t' X.chunkCount, hpiece, hmod]
  exact ⟨rfl, by omega⟩

/-- Proof of Theorem 17: "A failed scan [...] contains a c ∈ C_k with S(a,b,c) ≡ 0 (mod p) but
S(a,b,c) ≠ 0". -/
theorem exists_false_positive (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t)
    (hacc : X.acc t i = true) (hhit : X.hit t i = false) :
    ∃ c < X.len t, (X.p : ℤ) ∣ X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) ∧
      X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) ≠ 0 := by
  obtain ⟨c, hc, hdvd⟩ := (acc_iff hv ht hi).1 hacc
  refine ⟨c, hc, hdvd, fun hzero => ?_⟩
  rw [(hit_iff hi).2 ⟨c, hc, hzero⟩] at hhit
  exact absurd hhit (by decide)

/-- A vertex of the piece of an instance determines the number of the piece. -/
theorem c0_add_div {t c : ℕ} (hc : c < X.len t) : (X.c0 t + c) / X.q = t / X.chunkCount := by
  rw [c0, Nat.mul_add_div_of_lt (hc.trans_le (X.len_le t))]

/-- The length of a filtered range, as the size of a set. -/
private theorem length_filter_range (k : ℕ) (f : ℕ → Bool) :
    ((List.range k).filter f).length = #{i ∈ range k | f i = true} := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range]

/-- Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans". -/
theorem sum_fails_le (hv : X.Valid) :
    ∑ t ∈ range X.m, X.fails t ≤ (triOf X.n X.AB X.BC X.AC).F X.p := by
  -- The failed scans, as a set of pairs (instance, query pair).
  set failed : Finset (Σ _ : ℕ, ℕ) :=
    (range X.m).sigma fun t => {i ∈ range (X.w t) | (X.acc t i && !X.hit t i) = true} with hfailed
  have hcard : ∑ t ∈ range X.m, X.fails t = failed.card := by
    rw [hfailed, Finset.card_sigma]
    exact Finset.sum_congr rfl fun t _ => length_filter_range _ _
  have hmem : ∀ z ∈ failed,
      z.1 < X.m ∧ z.2 < X.w z.1 ∧ X.acc z.1 z.2 = true ∧ X.hit z.1 z.2 = false := by
    intro z hz
    simpa [hfailed, and_assoc] using hz
  rw [hcard]
  -- The scan `z` contains the triples of its query pair and a vertex of its piece.
  refine TriangleInstance.card_le_F_of_distinct_scans _ failed
    (fun z τ => τ.1.val = X.rowOf z.1 z.2 ∧ τ.2.1.val = X.colOf z.1 z.2 ∧
      ∃ c < X.len z.1, τ.2.2.val = X.c0 z.1 + c) (fun z hz => ?_) ?_
  · obtain ⟨ht, hi, hacc, hhit⟩ := hmem z hz
    obtain ⟨c, hc, hdvd, hne⟩ := exists_false_positive hv ht hi hacc hhit
    have hpiece := hv.piece_le ht
    exact ⟨(⟨_, hv.rowOf_lt ht hi⟩, ⟨_, hv.colOf_lt ht hi⟩, ⟨X.c0 z.1 + c, by omega⟩),
      ⟨rfl, rfl, c, hc, rfl⟩, hne, hdvd⟩
  · rintro τ z hz z' hz' ⟨hrow, hcol, c, hc, hvertex⟩ ⟨hrow', hcol', c', hc', hvertex'⟩
    obtain ⟨ht, hi, -, -⟩ := hmem z hz
    obtain ⟨ht', hi', -, -⟩ := hmem z' hz'
    have hplace : X.place z.1 z.2 = X.place z'.1 z'.2 := by
      rw [← rowOf_mul_add_colOf, ← rowOf_mul_add_colOf, ← hrow, ← hcol, hrow', hcol']
    have hpiece : z.1 / X.chunkCount = z'.1 / X.chunkCount := by
      rw [← c0_add_div hc, ← c0_add_div hc', ← hvertex, hvertex']
    obtain ⟨ht_eq, hi_eq⟩ := hv.eq_of_place_eq ht ht' hi hi' hplace hpiece
    exact Sigma.ext ht_eq (heq_of_eq hi_eq)

end HostData

end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the time of a run is within the worst case

The host procedure `et17` (Exact Triangle by Theorem 17) first computes the parameters, chooses the
prime and computes the sizes.  The time of what follows (the table of doubles, the residues, the
classes, the chunks and the loop over the instances; `hostRunTime`) depends on the data: the prime,
the number of chunks, the scans.  Here it is bounded by the corresponding summands of `hostMain`,
which depend on `n`, `U`, `D` and `g` only (`hostRunTime_le`).

* The prime is at most `√D` (`hostData_p_le`), and there are at most `4ng` instances and no more
  chunks than instances (`hostData_m_le`, `HostTime.chunkCount_le_m`).
* An instance has a piece of at most `q = ⌈s/g⌉` vertices, where `s = ⌊√D⌋`, and at most `⌊n²/√D⌋`
  query pairs, so its time without the scans is at most the worst case (`HostTime.instance_le`).
* All scans but one fail, and a failed scan belongs to a false positive of the chosen prime.  The
  proof of Theorem 17 bounds their number (`F_le_falsePositiveBound`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The number of false positives of the chosen prime is at most `falsePositiveBound`. -/
theorem F_le_falsePositiveBound {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) :
    (triOf x.n x.AB x.BC x.AC).F (chosenPrime x.n D x.AB x.BC x.AC)
      ≤ falsePositiveBound x.n x.U D :=
  Nat.le_floor (F_chosenPrime_le h.sixteen_le h.le_n hpre.U_pos hpre.leAB hpre.leBC hpre.leAC)

namespace HostTime

/-! ## One instance -/

/-- Writing the two matrices of an instance takes longer for a longer piece. -/
private theorem tWrites_mono (n D : ℕ) {a b : ℕ} (h : a ≤ b) : tWrites n D a ≤ tWrites n D b := by
  unfold tWrites tWriteX tWriteY
  gcongr

/-- The time of the solver on an instance with at most `cap` query pairs is at most `supTime`, its
largest time on such instances. -/
private theorem le_supTime (Tn : List ℕ → ℕ) (n D : ℕ) {w cap : ℕ} (h : w ≤ cap) :
    Tn [n, D, w] ≤ supTime Tn n D cap :=
  Finset.le_sup (f := fun w => Tn [n, D, w]) (Finset.mem_range.2 (by omega))

/-- The time of an instance with a piece of `len ≤ q` vertices, `w ≤ cap` query pairs and `execs`
scans is at most the worst case for `q` and `cap` plus the time of the scans. -/
private theorem instance_le (Tn : List ℕ → ℕ) (n D execs : ℕ) {len q w cap : ℕ} (hlen : len ≤ q)
    (hw : w ≤ cap) :
    tWrites n D len + Tn [n, D, w] + tScanPairs w len execs
      ≤ tWrites n D q + supTime Tn n D cap + tAnswers cap + tScanCall q * execs := by
  have hwrites := tWrites_mono n D hlen
  have hsolver := le_supTime Tn n D hw
  have hanswers : tAnswers w ≤ tAnswers cap := by
    unfold tAnswers
    gcongr
  have hscans : tScanCall len * execs ≤ tScanCall q * execs := by
    unfold tScanCall tScan
    gcongr
  unfold tScanPairs
  omega

/-- A sum of `m ≤ M` terms `f t ≤ A + B e(t)` is at most `M A + B E` if the `e(t)` add up to at most
`E`. -/
private theorem sum_le_mul_add {m M A B E : ℕ} {f e : ℕ → ℕ} (hf : ∀ t < m, f t ≤ A + B * e t)
    (hm : m ≤ M) (he : ∑ t ∈ Finset.range m, e t ≤ E) :
    ∑ t ∈ Finset.range m, f t ≤ M * A + B * E :=
  calc ∑ t ∈ Finset.range m, f t ≤ ∑ t ∈ Finset.range m, (A + B * e t) :=
        Finset.sum_le_sum fun t ht => hf t (Finset.mem_range.1 ht)
    _ = m * A + B * ∑ t ∈ Finset.range m, e t := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.mul_sum]
    _ ≤ M * A + B * E := Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_left _ he)

/-! ## The data of a run -/

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

/-- There are at most as many chunks as instances. -/
private theorem chunkCount_le_m {X : HostData} (hv : X.Valid) : X.chunkCount ≤ X.m := by
  have hn := hv.n_pos
  have hq := hv.q_pos
  have hpieces : 1 ≤ X.h := by
    rw [HostData.h, Nat.ceilDiv_eq_add_pred_div, Nat.le_div_iff_mul_le (by omega)]
    omega
  rw [HostData.m]
  exact Nat.le_mul_of_pos_left _ hpieces

/-- All scans but one fail, and there are at most `falsePositiveBound` failed scans. -/
private theorem sum_execs_le_falsePositiveBound (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) :
    ∑ t ∈ Finset.range (hostData x D g).m, (hostData x D g).execs t
      ≤ falsePositiveBound x.n x.U D + 1 :=
  (hostData x D g).sum_execs_le.trans (Nat.add_le_add_right
    ((HostData.sum_fails_le (hostData_valid hpre hbig)).trans
      (F_le_falsePositiveBound hpre hbig)) 1)

end HostTime

open HostTime

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

/-- The time of the loop over the instances is within its bound.  Both sides are a sum over the
instances plus the same constant; the piece of an instance has `min q (n - c₀)` vertices. -/
private theorem tHostLoop_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    tHostLoop Tn (hostData x D g) ≤ hostLoopBound Tn x.n x.U D g :=
  Nat.add_le_add_right (sum_le_mul_add
    (fun _ ht => instance_le Tn x.n D _ (Nat.min_le_left _ _) ((hostData x D g).w_le_cap ht))
    (hostData_m_le hbig) (sum_execs_le_falsePositiveBound hpre hbig)) 14

/-- **The time of a run after the choice of the prime is within the worst case.** -/
theorem hostRunTime_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    hostRunTime Tn (hostData x D g) x.U
      ≤ tDblTable (bitLen x.U) + 3 * tResidues (x.n * x.n) (bitLen x.U)
        + tClasses x.n (Nat.sqrt D) + tChunks (Nat.sqrt D) (4 * x.n * g)
        + hostLoopBound Tn x.n x.U D g + 80 := by
  have hprime : (hostData x D g).p ≤ Nat.sqrt D := hostData_p_le x g hbig.sixteen_le
  have hchunks : (hostData x D g).chunkCount ≤ 4 * x.n * g :=
    (chunkCount_le_m (hostData_valid hpre hbig)).trans (hostData_m_le hbig)
  have hloop := tHostLoop_le hpre hbig Tn
  have hn : (hostData x D g).n = x.n := rfl
  unfold hostRunTime
  rw [hn]
  unfold tClasses tChunks
  omega

end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: et17 decides Exact Triangle

The three parts of the host procedure `et17` (Exact Triangle by Theorem 17) and the small case are
put together (`et17_spec`).  Correctness is `HostData.found_m`: a zero triangle is found if and only
if there is one.
-/

public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-- **et17 decides Exact Triangle.**  In every program `P₀ ++ R` that satisfies the context
`Et17Ctx` (it holds the solver, the procedures of the host and the two parameter procedures), on an
instance with `x.Pre μ fr` and within limits that allow for `hostNeed`, the body of et17 ends within
`hostTime` steps in a state that satisfies `etTask.Post`. -/
theorem et17_spec_sourceProof {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    {lim : Limits} {d : ℕ} (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Body ν) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩
      (hostTime Dfun Gfun tD tG Tn x.n x.U) fun σ' => etTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hparams := et17Params_spec C x μ fr hpre hok
  have hone : (1 : ℤ) ≤ lim.word := by
    have hword := hok.word
    simp only [hostNeed, hostNeedAt, hostWord] at hword
    omega
  rw [← frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr] 29]
  unfold hostNeed at hok
  unfold et17Body hostTime hostSetup
  generalize Dfun x.n = D at *
  generalize Gfun D = g at *
  -- the parameters
  refine Ends.next _ (hparams.mono le_rfl ?_) (by omega)
  rintro _ rfl
  -- if n is small: the brute force
  by_cases hs : SmallCase x.n D g
  · rw [if_pos hs]
    exact Ends.iteLast (fun _ => (et17Small_spec C x μ fr D g _ _ hpre hok).mono
      (by simp; omega) fun _ h => h) (fun h => absurd (by simp [et17LocA, hs]) h) (by simp; omega)
  rw [if_neg hs]
  refine Ends.iteLast (fun h => absurd h (by simp [et17LocA, hs])) (fun _ => ?_) (by simp; omega)
  -- otherwise: the sizes, then the tables and the loop over the instances
  have hbig := not_smallCase_iff.1 hs
  have htime := hostRunTime_le hpre hbig Tn
  refine Ends.next _ ((et17Sizes_spec C x μ fr D g _ _ hpre hbig hok).mono le_rfl ?_)
    (by unfold hostMain; simp; omega)
  rintro _ ⟨μ', rfl, hk⟩
  refine (et17Tables_spec C x μ' fr D g _ _ (hpre.keep hk) hbig hok).mono
    (by unfold hostMain; simp; omega) ?_
  rintro σ'' ⟨hresult, hk'⟩
  refine ⟨?_, fun a ha => (hk' a ha).trans (hk a ha)⟩
  rw [hresult, HostData.found_m (hostData_valid hpre hbig), ← flag_eq_bit]
  exact flag_congr (hasZero_iff x.n x.AB x.BC x.AC)

end Light.Sec3

end
end


theorem solution : ∀ {P₀ R : Light.Program} {ν : Light.Sec3.Et17Nums} {Tn : List.{0} Nat → Nat} {need : List.{0} Nat → Light.Need}
  {Dfun Gfun tD tG wD wG : Nat → Nat},
  Light.Sec3.Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG →
    ∀ {lim : Light.Limits} {d : Nat} (x : Light.TriInst) (μ : Nat → Int) (fr : Nat),
      x.Pre μ fr →
        (Light.Sec3.hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr d →
          Light.Ends lim
            (@HAppend.hAppend.{0, 0, 0} Light.Program Light.Program Light.Program
              (@instHAppendOfAppend.{0} Light.Program (@List.instAppend.{0} Light.Stmt)) P₀ R)
            d (Light.Sec3.et17Body ν)
            {
              loc :=
                Light.frame
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x.n)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x.U)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x.ab)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x.bc)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x.ac)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr) (@List.nil.{0} Int))))))),
              mem := μ }
            (Light.Sec3.hostTime Dfun Gfun tD tG Tn x.n x.U) fun (σ' : Light.State) =>
            Light.etTask.Post x μ fr (σ'.loc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) σ'.mem := by
  exact @Light.Sec3.et17_spec_sourceProof

#print axioms solution
