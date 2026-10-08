-- Prove2me | solution 1 for Light.Sec3.et17Tables_spec
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:21:08.684214+00:00
-- url     : https://prove2.me/submissions/a8b98be5-a9f9-415b-98b8-d1f1772aeb77

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
import Definitions.Def_APSPSource_ThreeSumApsp_Util_CountingSort
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
import Theorems.Thm_List_getD_filter_range_count
import Theorems.Thm_ThreeSumApsp_Spec_length_chunkTab_le
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

/-- A weaker conclusion. -/
theorem Stmt.Runs.mono {s : Stmt} {σ : State} {R R' : State → Prop} (h : s.Runs lim σ R)
    (hR : ∀ σ', R σ' → R' σ') : s.Runs lim σ R' :=
  ⟨h.1, hR _ h.2⟩


















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

theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl

theorem SameOn.trans (h₁ : SameOn K μ μ') (h₂ : SameOn K μ' μ'') : SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)















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

/-- The list of the `j < n` with `q j` has `Nat.count q n` members. -/
theorem length_filter_range (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    ((List.range n).filter fun j => decide (q j)).length = Nat.count q n := by
  rw [Nat.count, List.countP_eq_length_filter]






































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
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_54037_0 apspMacro_54037_1);
                                                                                  (first
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_54037_2));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_54037_2 apspMacro_54037_0 (by omega)));
                                                                                                  (revert apspMacro_54037_2)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((simp [] at apspMacro_54037_1);
                                                                                        (((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_54037_3));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_54037_3 apspMacro_54037_0 (by omega)));
                                                                                                  (revert apspMacro_54037_3)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_54037_4));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_54037_4 apspMacro_54037_0 (by omega)));
                                                                                                  (revert apspMacro_54037_4)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (fail
                                                                                            "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                      SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                      its condition K x does not follow from the hypotheses."))))) :
    Seg μ' a l :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩










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







/-- A piece of a segment of natural numbers: w cells from the place lo on. -/
theorem SegN.drop_take {l : List ℕ} (h : SegN μ a l) (lo w : ℕ) :
    SegN μ (a + lo) ((l.drop lo).take w) := by
  simpa only [SegN, List.map_take, List.map_drop] using (Seg.drop h lo).take w

/-- A segment of natural numbers stays where it is if its cells do not change. -/
theorem SegN.keep {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_56122_0 apspMacro_56122_1);
                                                    (first
                                                      |
                                                        ((((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_56122_2));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_56122_2 apspMacro_56122_0 (by omega)));
                                                                    (revert apspMacro_56122_2)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (omega))
                                                      |
                                                        ((simp [] at apspMacro_56122_1);
                                                          (((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_56122_3));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_56122_3 apspMacro_56122_0 (by omega)));
                                                                    (revert apspMacro_56122_3)));
                                                              (intros);
                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                          (omega))
                                                      |
                                                        ((((repeat
                                                                  (((with_reducible
                                                                          rename Light.SameOn _ _ _ => apspMacro_56122_4));
                                                                    ((try
                                                                          have :=
                                                                            apspMacro_56122_4 apspMacro_56122_0 (by omega)));
                                                                    (revert apspMacro_56122_4)));
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
























































































/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/































/-- A solver meets the specification of its task, at the depth d at which it runs. -/
theorem SolvesN.meets {task : TaskN} {P₀ : Program} {p : ℕ} {T₀ : List ℕ → ℕ}
    {need : List ℕ → Need} (h : SolvesN task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ}
    (x : task.Inst) {μ : ℕ → ℤ} {fr : ℕ} (hpre : task.Pre x μ fr)
    (hok : (need (task.pars x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.pars x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩






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
                            (intro apspMacro_108327_0 apspMacro_108327_1);
                            (first
                              |
                                ((((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ =>
                                                    apspMacro_108327_2));
                                            ((try
                                                  have :=
                                                    apspMacro_108327_2
                                                      apspMacro_108327_0
                                                      (by omega)));
                                            (revert apspMacro_108327_2)));
                                      (intros);
                                      (try
                                          simp only [Function.update_apply,
                                            Light.wrote] at *)));
                                  (omega))
                              |
                                ((simp [length_dblList] at apspMacro_108327_1);
                                  (((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ =>
                                                    apspMacro_108327_3));
                                            ((try
                                                  have :=
                                                    apspMacro_108327_3
                                                      apspMacro_108327_0
                                                      (by omega)));
                                            (revert apspMacro_108327_3)));
                                      (intros);
                                      (try
                                          simp only [Function.update_apply,
                                            Light.wrote] at *)));
                                  (omega))
                              |
                                ((((repeat
                                          (((with_reducible
                                                  rename Light.SameOn _ _ _ =>
                                                    apspMacro_108327_4));
                                            ((try
                                                  have :=
                                                    apspMacro_108327_4
                                                      apspMacro_108327_0
                                                      (by omega)));
                                            (revert apspMacro_108327_4)));
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
                          (intro apspMacro_108327_5 apspMacro_108327_6);
                          (first
                            |
                              ((((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ =>
                                                  apspMacro_108327_7));
                                          ((try
                                                have :=
                                                  apspMacro_108327_7
                                                    apspMacro_108327_5 (by omega)));
                                          (revert apspMacro_108327_7)));
                                    (intros);
                                    (try
                                        simp only [Function.update_apply,
                                          Light.wrote] at *)));
                                (omega))
                            |
                              ((simp [length_dblList] at apspMacro_108327_6);
                                (((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ =>
                                                  apspMacro_108327_8));
                                          ((try
                                                have :=
                                                  apspMacro_108327_8
                                                    apspMacro_108327_5 (by omega)));
                                          (revert apspMacro_108327_8)));
                                    (intros);
                                    (try
                                        simp only [Function.update_apply,
                                          Light.wrote] at *)));
                                (omega))
                            |
                              ((((repeat
                                        (((with_reducible
                                                rename Light.SameOn _ _ _ =>
                                                  apspMacro_108327_9));
                                          ((try
                                                have :=
                                                  apspMacro_108327_9
                                                    apspMacro_108327_5 (by omega)));
                                          (revert apspMacro_108327_9)));
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





























































/-! ## The product and the count -/
































































































end parts

/-! ## Larger primes need more cells and more time -/

















end Light.Sec3

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

















/-! ## The routine -/

namespace ScanPairs

















end ScanPairs



































section

variable {pScan : ℕ} {μ : ℕ → ℤ} {out qa qb w ab bc ac n c0 len U : ℕ} {OUT AB BC AC : List ℤ}
  {QA QB : List ℕ} {f : Bool}














/-- One query pair: a scan is made if the pair is accepted and nothing has been found yet. -/
theorem scanPairsStep_spec (hp : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (A : Answers lim μ out qa qb w n OUT QA QB)
    (hd : d < lim.depth) (hc : c0 + len ≤ n) {i : ℕ} (hi : i < w) :
    Ends lim P d (scanPairsStep pScan)
      (scanPairsState μ out qa qb w ab bc ac n c0 len OUT AB BC AC QA QB f i i)
      (11 + if execAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f i then tScanCall len else 0)
      (· = scanPairsState μ out qa qb w ab bc ac n c0 len OUT AB BC AC QA QB f (i + 1) i) := by
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.arrAB); (obtain ⟨⟩ := id C.arrBC);
    (obtain ⟨⟩ := id C.arrAC))
  ((obtain ⟨⟩ := id A); (obtain ⟨⟩ := id A.arrOUT); (obtain ⟨⟩ := id A.arrQA);
    (obtain ⟨⟩ := id A.arrQB))
  have hreadOUT := A.arrOUT.read hi
  have hreadQA := A.arrQA.read hi
  have hreadQB := A.arrQB.read hi
  have ha := A.arrQA.getD_lt hi
  have hb := A.arrQB.getD_lt hi
  unfold scanPairsStep scanPairsState
  rw [foundAt_succ, execAt, accOf, hitOf]
  -- The answer, the pair, and whether a zero triangle has been found before.
  generalize foundAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f i = found
  generalize OUT.getD i 0 = answer at hreadOUT ⊢
  generalize QA.getD i 0 = a at hreadQA ha ⊢
  generalize QB.getD i 0 = b at hreadQB hb ⊢
  -- if out[i] = 0
  by_cases hz : answer = 0
  · exact Ends.iteLast (fun _ => Ends.skip (by simp [hz]))
      (fun h => absurd (by simp [hreadOUT, hz]) h) (by (((try have := Light.Std.space_le (by assumption)));
                                                         ((try have := Light.Std.const_le (by assumption)));
                                                         (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
  refine Ends.iteLast (fun h => absurd h (by simp [hreadOUT, hz])) (fun _ => ?_)
    (by (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
  -- if f = 0
  cases found
  · refine Ends.iteLast (fun _ => ?_) fun h => absurd (by simp [bit]) h
    -- f := scan(ab, bc, ac, n, qa[i], qb[i], c0, len)
    refine Ends.callTo (scan_meets hp C ha hb hc) ?_
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadQA, hreadQB] <;> omega)))
      (hT := by simp [hz, tScanCall]; omega)
    rintro _ _ ⟨rfl, rfl⟩
    simp [hz, flag_eq_bit]
  · exact Ends.iteLast (fun h => absurd h (by simp [bit])) fun _ => Ends.skip (by simp)

/-- The time of the rounds, added up: 19 steps for each query pair, and the scans. -/
theorem sum_scanPairs_rounds (acc hit : ℕ → Bool) (f : Bool) (len w : ℕ) :
    ∑ i ∈ Finset.range w, (4 + (15 + if execAt acc hit f i then tScanCall len else 0))
      = 19 * w + tScanCall len * execsUpto acc hit f w := by
  induction w with
  | zero => simp [execsUpto]
  | succ w ih =>
    rw [Finset.sum_range_succ, ih, execsUpto_succ]
    split_ifs <;> ring

/-- **scanPairs** returns the new value of `f`; no cell changes; the time depends on the number of
scans that are made. -/
theorem scanPairs_spec (hp : P[pScan]? = some scanBody) (C : Weights lim μ ab bc ac n U AB BC AC)
    (A : Answers lim μ out qa qb w n OUT QA QB) (hd : d < lim.depth) (hc : c0 + len ≤ n) :
    Ends lim P d (scanPairsBody pScan) ⟨frame [out, qa, qb, w, bit f, ab, bc, ac, n, c0, len], μ⟩
      (tScanPairs w len (execsUpto (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f w)) fun σ' =>
      σ'.loc 0 = bit (foundAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f w) ∧ σ'.mem = μ := by
  ((obtain ⟨⟩ := id C); (obtain ⟨⟩ := id C.arrAB); (obtain ⟨⟩ := id C.arrBC);
    (obtain ⟨⟩ := id C.arrAC))
  ((obtain ⟨⟩ := id A); (obtain ⟨⟩ := id A.arrOUT); (obtain ⟨⟩ := id A.arrQA);
    (obtain ⟨⟩ := id A.arrQB))
  have hsum := sum_scanPairs_rounds (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f len w
  unfold tScanPairs tAnswers
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
            -- while i < w
            
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
  -- while i < w
  refine Ends.next _ (Ends.while
    (fun i σ => σ = scanPairsState μ out qa qb w ab bc ac n c0 len OUT AB BC AC QA QB f i i) w
    (fun i => 15 + if execAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f i then tScanCall len
      else 0) ?start ?round ?done) (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)
  case start => simp [scanPairsState, foundAt_zero]
  case round =>
    rintro i _ hi rfl
    refine ⟨by simp, by simp [scanPairsState]; omega, ?_⟩
    -- the query pair number i; then i := i + 1
    refine Ends.next _ ((scanPairsStep_spec hp C A hd hc hi).mono le_rfl ?_) (by omega)
    rintro _ rfl
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (i + 1 : ℕ) ?_ ?_ ?_);
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
    exact by simp [scanPairsState]
  case done =>
    rintro _ rfl
    -- return f
    exact ⟨by simp, by simp [scanPairsState],
      Ends.setTo (bit (foundAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f w)) ⟨rfl, rfl⟩
        (by simp) (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)⟩

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

/-- The chosen prime is at least 2. -/
theorem two_le_chosenPrime (hD : 16 ≤ D) : 2 ≤ chosenPrime n D AB BC AC :=
  (mem_primesList.1 (chosenPrime_mem_primesList AB BC AC hD)).1.two_le

/-- The chosen prime is at most `⌊√D⌋`. -/
theorem chosenPrime_le_sqrt (hD : 16 ≤ D) : chosenPrime n D AB BC AC ≤ Nat.sqrt D :=
  le_sqrt_of_mem_primesList (chosenPrime_mem_primesList AB BC AC hD)

end Chosen

/-! ## The smallest count, by one pass -/




















/-! ## False positives, in terms of a bound on the weights -/











































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

/-- The residue of a chunk is below `p`. -/
theorem Valid.rho_lt (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.rho t < X.p :=
  (hv.chunk_entry ht).residue_lt

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













































/-- The query pairs of an instance, from the places. -/
theorem zip_eq (X : HostData) (t : ℕ) :
    (X.WI t).zip (X.WJ t) =
      (((sortedIdx X.n X.p X.RAB).drop (X.lo t)).take (X.w t)).map fun s => (s / X.n, s % X.n) := by
  rw [WI, WJ, QI, QJ, queryRows, queryCols, ← List.map_drop, ← List.map_drop, ← List.map_take,
    ← List.map_take, List.zip_map']

/-- No query pair is listed twice. -/
theorem nodup_zip (X : HostData) (t : ℕ) : ((X.WI t).zip (X.WJ t)).Nodup := by
  rw [zip_eq]
  refine (((sortedIdx_nodup X.n X.p X.RAB).sublist (List.drop_sublist _ _)).sublist
    (List.take_sublist _ _)).map fun s s' h => ?_
  simp only [Prod.mk.injEq] at h
  rw [← Nat.div_add_mod s X.n, ← Nat.div_add_mod s' X.n, h.1, h.2]

/-- The rows of the query pairs are vertices of `A`. -/
theorem lt_of_mem_WI {t a : ℕ} (ha : a ∈ X.WI t) : a < X.n := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  exact Nat.div_lt_of_lt_mul' (lt_of_mem_sortedIdx hs)

/-- The columns of the query pairs are vertices of `B`. -/
theorem lt_of_mem_WJ {t b : ℕ} (hb : b ∈ X.WJ t) : b < X.n := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  exact Nat.mod_lt_of_lt_mul (lt_of_mem_sortedIdx hs)

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

/-- The matrix `X` has `n` rows and `D` columns. -/
theorem length_matX (X : HostData) (t : ℕ) : (X.matX t).length = X.n * X.D := by simp [matX, xList]

/-- The matrix `Y` has `D` rows and `n` columns. -/
theorem length_matY (X : HostData) (t : ℕ) : (X.matY t).length = X.D * X.n := by simp [matY, yList]

/-- The entries of `X` are 0 and 1. -/
theorem matX_zero_or_one (X : HostData) (t : ℕ) : ∀ e ∈ X.matX t, e = 0 ∨ e = 1 := by
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  exact (ite_eq_or_eq _ _ _).symm

/-- The entries of `Y` are 0 and 1. -/
theorem matY_zero_or_one (X : HostData) (t : ℕ) : ∀ e ∈ X.matY t, e = 0 ∨ e = 1 := by
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  exact (ite_eq_or_eq _ _ _).symm








































/-! ## Acceptance -/

















































































































/-! ## Correctness -/

























































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
# The two matrices of an instance (proof of Theorem 17)

"a ∼ (c, σ) ⟺ σ ≡ w(a,c) + ϱ, (c, σ) ∼ b ⟺ σ ≡ -w(b,c) (mod p)."

writeY(y, rbc, n, D, p, c0, len) writes the D × n matrix Y of the instances for the piece
{c0, …, c0 + len - 1} of C: the middle vertex (c, σ) is the row (c - c0) p + σ.  The n² cells from
rbc hold the residues of the weights w(b,c) mod p, that of (b, c) at place b n + c.
writeX(x, rac, n, D, p, c0, len, rho) writes the n × D matrix X for the residue rho; the cells from
rac hold the residues of the weights w(a,c), that of (a, c) at place a n + c.  In the statements and
docstrings below, c counts from 0 within the piece: the c-th member of the piece is the vertex
c0 + c.

Both clear the matrix and then run through the pairs of a vertex and a member of the piece; each
pair marks one cell with a 1.  So both are instances of one pair of loops:

* `markVal` says what a cell holds when the pairs before (u, w) have been handled, and `Marked` says
  it of the memory;
* `markPairs` runs the two loops, given what the body does for one pair (`MarkCtx`);
* `writeYCell_spec` and `writeXCell_spec` treat the bodies: read a residue, form the label, mark the
  cell;
* `getElem_yList` and `getElem_xList` identify the marks of all pairs with the matrices.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Marking cells: the pure side -/

section marks












variable {pos : ℕ → ℕ → ℕ} {W u w i : ℕ}

theorem markVal_zero : markVal pos W 0 0 i = 0 := by
  unfold markVal
  rw [if_neg]
  rintro ⟨u', w', h, -, -⟩
  omega

theorem markVal_step (hlt : w < W) :
    markVal pos W u (w + 1) i = if i = pos u w then 1 else markVal pos W u w i := by
  unfold markVal
  by_cases h : i = pos u w
  · rw [if_pos h, if_pos ⟨u, w, Or.inr ⟨rfl, by omega⟩, hlt, h.symm⟩]
  · rw [if_neg h]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨u', w', h1, h2, h3⟩
      refine ⟨u', w', ?_, h2, h3⟩
      rcases h1 with h1 | ⟨rfl, h1⟩
      · exact Or.inl h1
      · refine Or.inr ⟨rfl, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h4 | rfl
        · exact h4
        · exact absurd h3.symm h
    · rintro ⟨u', w', h1, h2, h3⟩
      exact ⟨u', w', by omega, h2, h3⟩

theorem markVal_row : markVal pos W u W i = markVal pos W (u + 1) 0 i := by
  unfold markVal
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u', w', h1, h2, h3⟩
    exact ⟨u', w', by omega, h2, h3⟩
  · rintro ⟨u', w', h1, h2, h3⟩
    exact ⟨u', w', by omega, h2, h3⟩

/-- At the end, a cell is marked iff it is the cell of one of the pairs. -/
theorem markVal_end {U : ℕ} (q : Prop) [Decidable q] (h : q ↔ ∃ u' < U, ∃ w' < W, pos u' w' = i) :
    markVal pos W U 0 i = if q then 1 else 0 := by
  unfold markVal
  have : CellMarked pos W U 0 i ↔ q := by
    rw [h]
    constructor
    · rintro ⟨u', w', h1, h2, h3⟩
      exact ⟨u', by omega, w', h2, h3⟩
    · rintro ⟨u', h1, w', h2, h3⟩
      exact ⟨u', w', Or.inl h1, h2, h3⟩
  by_cases hq : q
  · rw [if_pos hq, if_pos (this.2 hq)]
  · rw [if_neg hq, if_neg fun h' => hq (this.1 h')]

end marks

/-! ## Marking cells: the memory -/







namespace Marked

variable {μ μ' : ℕ → ℤ} {base m : ℕ} {pos : ℕ → ℕ → ℕ} {U W u w : ℕ}

/-- After the clearing no pair has been handled. -/
theorem start (hzero : ∀ i < m, μ' (base + i) = 0) (hrest : SameOutside μ μ' base m) :
    Marked μ μ' base m pos W 0 0 :=
  ⟨fun i hi => by rw [markVal_zero]; exact hzero i hi, hrest⟩

/-- The pair (u, w) marks its cell. -/
theorem step (h : Marked μ μ' base m pos W u w) (hlt : w < W) (hpos : pos u w < m) :
    Marked μ (Function.update μ' (base + pos u w) 1) base m pos W u (w + 1) := by
  refine ⟨fun i hi => ?_, h.rest.update ⟨by omega, by omega⟩ _⟩
  rw [markVal_step hlt]
  split_ifs with e
  · rw [e, Function.update_self]
  · rw [Function.update_of_ne (by omega)]
    exact h.cells i hi

/-- The end of a row of pairs is the beginning of the next row. -/
theorem row (h : Marked μ μ' base m pos W u W) : Marked μ μ' base m pos W (u + 1) 0 :=
  ⟨fun i hi => by rw [← markVal_row]; exact h.cells i hi, h.rest⟩

/-- When all pairs have been handled, the cells hold the list of all marks. -/
theorem seg {l : List ℤ} (h : Marked μ μ' base m pos W U 0) (hlen : l.length = m)
    (hget : ∀ i (hi : i < l.length), l[i] = markVal pos W U 0 i) : Seg μ' base l :=
  fun i hi => by rw [hget i hi]; exact h.cells i (hlen ▸ hi)

end Marked

/-! ## Marking cells: the two loops -/




















section loops

variable {μ μ' : ℕ → ℤ} {base m U W b : ℕ} {pos : ℕ → ℕ → ℕ} {cu cw : ℕ} {hiU hiW : Expr}
  {cell : Stmt} {L : ℤ → ℤ → ℤ → List ℤ}

/-- The inner loop: the pairs (u, 0), …, (u, W - 1) mark their cells. -/
theorem markRow (C : MarkCtx lim P d μ base m U W b pos cu cw hiU hiW cell L) {u : ℕ} (hu : u < U)
    (w₀ t₀ : ℤ) (h : Marked μ μ' base m pos W u 0) :
    Ends lim P d (.for cw hiW cell) ⟨frame (L u w₀ t₀), μ'⟩ (W * (hiW.cost + b + 7) + hiW.cost + 5)
      fun σ' => ∃ w t μ'', σ' = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W (u + 1) 0 := by
  refine Ends.for
    (fun w σ => ∃ t μ'', σ = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W u w) W b
    ?start ?round ?done ?bound C.wordW le_rfl
  case start => exact ⟨t₀, μ', by simp only [update_frame_setLocal, C.setW, Nat.cast_zero], h⟩
  case bound =>
    rintro w _ - - ⟨t, μ'', rfl, -⟩
    exact C.boundW _ _ _ _
  case round =>
    rintro w _ hlt - ⟨t, μ'', rfl, hm⟩
    refine (C.cell_spec u w t μ'' hu hlt hm.rest).mono le_rfl ?_
    rintro _ ⟨t', rfl⟩
    exact ⟨C.atW _ _ _, t', _,
      by simp only [update_frame_setLocal, C.setW, Nat.cast_add, Nat.cast_one],
      hm.step hlt (C.pos_lt u w hu hlt)⟩
  case done =>
    rintro _ - ⟨t, μ'', rfl, hm⟩
    exact ⟨W, t, μ'', rfl, hm.row⟩

/-- **The two loops**: all pairs mark their cells. -/
theorem markPairs (C : MarkCtx lim P d μ base m U W b pos cu cw hiU hiW cell L) (u₀ w₀ t₀ : ℤ)
    (h : Marked μ μ' base m pos W 0 0) :
    Ends lim P d (.for cu hiU (.for cw hiW cell)) ⟨frame (L u₀ w₀ t₀), μ'⟩
      (U * (hiU.cost + (W * (hiW.cost + b + 7) + hiW.cost + 5) + 7) + hiU.cost + 5)
      fun σ' => Marked μ σ'.mem base m pos W U 0 := by
  refine Ends.for
    (fun u σ => ∃ w t μ'', σ = ⟨frame (L u w t), μ''⟩ ∧ Marked μ μ'' base m pos W u 0) U _
    ?start ?round ?done ?bound C.wordU le_rfl
  case start => exact ⟨w₀, t₀, μ', by simp only [update_frame_setLocal, C.setU, Nat.cast_zero], h⟩
  case bound =>
    rintro u _ - - ⟨w, t, μ'', rfl, -⟩
    exact C.boundU _ _ _ _
  case round =>
    rintro u _ hu - ⟨w, t, μ'', rfl, hm⟩
    refine (markRow C hu w t hm).mono le_rfl ?_
    rintro _ ⟨w', t', μ₃, rfl, hm'⟩
    exact ⟨C.atU _ _ _, w', t', μ₃,
      by simp only [update_frame_setLocal, C.setU, Nat.cast_add, Nat.cast_one], hm'⟩
  case done =>
    rintro _ - ⟨w, t, μ'', rfl, hm⟩
    exact hm

end loops

/-! ## Clearing the matrix -/

/-- The loop that clears a matrix: local 0 holds its address base, local t the number m of its
cells, and local c is the counter.  Afterwards the m cells hold 0, and no other cell has changed. -/
theorem clear_spec {μ : ℕ → ℤ} {l : List ℤ} {c t base m : ℕ} {Q : State → Prop}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : base + m < lim.space) (hc : 0 ≠ c) (ht : t ≠ c)
    (hbase : frame l 0 = base) (hm : frame l t = m)
    (h : ∀ μ', (∀ i < m, μ' (base + i) = 0) → SameOutside μ μ' base m →
      Q ⟨frame (setLocal l c m), μ'⟩) :
    Ends lim P d (.for c (v t) (.store (((Light.Expr.op Light.Op.add) (v 0) (v c))) (k 0))) ⟨frame l, μ⟩ (13 * m + 6) Q := by
  refine Ends.pass (x := t) (y := 0) (dst := base) (n := m) (fun _ => 0)
    (fun j _ => ⟨?_, by simp⟩) ?_ hw (by omega) hm hbase ht hc
  · change ((0 : ℕ) : ℤ) ≤ lim.word
    omega
  · rw [update_frame_setLocal]
    exact h _ (fun i hi => wrote_done hi) (sameOutside_wrote le_rfl)

/-! ## What both routines assume -/


















namespace WritePre

variable {μ μ' : ℕ → ℤ} {base m res n D p c0 len : ℕ} {R : List ℕ}

/-- The number n of vertices fits in a word. -/
theorem n_le_word (pre : WritePre lim μ base m res n D p c0 len R) : (n : ℤ) ≤ lim.word := by
  have := pre.hw
  have := pre.spaceR
  have := Nat.le_mul_self n
  omega

/-- The length of the piece fits in a word. -/
theorem len_le_word (pre : WritePre lim μ base m res n D p c0 len R) : (len : ℤ) ≤ lim.word := by
  have := pre.n_le_word
  have := pre.piece
  omega

/-- The place of the weight between the vertex u and the c-th member c0 + c of the piece. -/
theorem index_lt (pre : WritePre lim μ base m res n D p c0 len R) {u c : ℕ} (hu : u < n)
    (hc : c < len) : u * n + c0 + c < n * n := by
  have := pre.piece
  have := Nat.mul_add_lt_mul hu (show c0 + c < n by omega)
  omega

/-- The residues can be read at any time. -/
theorem read (pre : WritePre lim μ base m res n D p c0 len R) (h : SameOutside μ μ' base m) {i : ℕ}
    (hi : i < n * n) : μ' (res + i) = (R.getD i 0 : ℕ) := by
  have hap := pre.apart
  have hil : i < R.length := pre.length ▸ hi
  rw [h _ (by omega), pre.seg _ (by simpa using hil), List.getElem_map,
    List.getD_eq_getElem _ 0 hil]

/-- The residues are below p. -/
theorem getD_lt (pre : WritePre lim μ base m res n D p c0 len R) {i : ℕ} (hi : i < n * n) :
    R.getD i 0 < p := by
  have hil : i < R.length := pre.length ▸ hi
  rw [List.getD_eq_getElem _ 0 hil]
  exact pre.lt _ (List.getElem_mem hil)

/-- The label s of the c-th member of the piece is one of the D middle vertices. -/
theorem middle_lt (pre : WritePre lim μ base m res n D p c0 len R) {c s : ℕ} (hc : c < len)
    (hs : s < p) : c * p + s < D :=
  (Nat.mul_add_lt_mul hc hs).trans_le pre.fits

end WritePre

/-! ## The matrix Y -/

namespace WriteY
















end WriteY

























/-- Entry i of yList, the matrix Y row by row, is 1 if one of the pairs (c, b) marks the cell i, and
0 if not. -/
theorem getElem_yList {n D p c0 len : ℕ} {RBC : List ℕ} (hp : 0 < p) {i : ℕ}
    (hi : i < (yList n D p c0 len RBC).length) :
    (yList n D p c0 len RBC)[i] = markVal (posY n p c0 RBC) n len 0 i := by
  have hi' : i < D * n := by simpa [yList] using hi
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi'
  rw [markVal_end
    (i / n / p < len ∧ i / n % p = (p - RBC.getD (i % n * n + c0 + i / n / p) 0) % p)]
  · simp [yList]
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨i / n / p, h1, i % n, Nat.mod_lt _ hn, ?_⟩
      rw [posY, labY, ← h2, Nat.mul_comm (i / n / p) p, Nat.div_add_mod, Nat.mul_comm (i / n) n,
        Nat.div_add_mod]
    · rintro ⟨c, hc, b, hb, rfl⟩
      have hl : labY n p c0 RBC c b < p := Nat.mod_lt _ hp
      rw [posY, Nat.mul_add_div_of_lt hb, Nat.mul_add_mod_of_lt hb, Nat.mul_add_div_of_lt hl,
        Nat.mul_add_mod_of_lt hl]
      exact ⟨hc, rfl⟩

section writeY

variable {μ μ' : ℕ → ℤ} {y rbc n D p c0 len : ℕ} {RBC : List ℕ}

/-- The cell of a pair lies in the matrix. -/
theorem posY_lt (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) {c b : ℕ} (hc : c < len)
    (hb : b < n) : posY n p c0 RBC c b < D * n := by
  have hp := pre.getD_lt (pre.index_lt hb hc)
  exact Nat.mul_add_lt_mul (pre.middle_lt hc (Nat.mod_lt _ (by omega))) hb

/-- The label, as the program computes it. -/
theorem labY_eq {c b : ℕ} (hr : RBC.getD (b * n + c0 + c) 0 < p) : labY n p c0 RBC c b =
    if RBC.getD (b * n + c0 + c) 0 = 0 then 0 else p - RBC.getD (b * n + c0 + c) 0 := by
  unfold labY
  split_ifs with h
  · rw [h, Nat.sub_zero, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

open WriteY in
/-- **One pair of writeY.** -/
theorem writeYCell_spec (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) {c b : ℕ} (t : ℤ)
    (hc : c < len) (hb : b < n) (hrest : SameOutside μ μ' y (D * n)) :
    Ends lim P d writeYCell ⟨frame [y, rbc, n, D, p, c0, len, c, b, t, (D * n : ℕ)], μ'⟩ 32
      fun σ' => ∃ t', σ' = ⟨frame [y, rbc, n, D, p, c0, len, c, b, t', (D * n : ℕ)],
        Function.update μ' (y + posY n p c0 RBC c b) 1⟩ := by
  (obtain ⟨⟩ := id pre)
  have hidx := pre.index_lt hb hc
  have hread := pre.read hrest hidx
  have hr := pre.getD_lt hidx
  have hlab := labY_eq hr
  have hpos : (c * p + labY n p c0 RBC c b) * n + b < D * n := posY_lt pre hc hb
  have hrow : c * p + labY n p c0 RBC c b < D := pre.middle_lt hc (Nat.mod_lt _ (by omega))
  have hDn : D ≤ D * n := Nat.le_mul_of_pos_right D (by omega)
  have hposZ : ((c : ℤ) * p + labY n p c0 RBC c b) * n + b < D * n := by exact_mod_cast hpos
  have hpos0 : 0 ≤ ((c : ℤ) * p + labY n p c0 RBC c b) * n := by positivity
  have haddr : ((rbc : ℤ) + b * n + c0 + c).toNat = rbc + (b * n + c0 + c) := by omega
  generalize RBC.getD (b * n + c0 + c) 0 = r at hread hr hlab
  -- y[(c p + r) n + b] := 1, once r is the label
  have mark : ∀ s : ℕ, labY n p c0 RBC c b = s →
      Ends lim P d (.store (((Light.Expr.op Light.Op.add)
                              ((Light.Expr.op Light.Op.add) (v Y)
                                ((Light.Expr.op Light.Op.mul)
                                  ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v C) (v PR))
                                    (v R))
                                  (v N)))
                              (v B))) (k 1))
        ⟨frame [y, rbc, n, D, p, c0, len, c, b, s, (D * n : ℕ)], μ'⟩ 13 fun σ' =>
          ∃ t', σ' = ⟨frame [y, rbc, n, D, p, c0, len, c, b, t', (D * n : ℕ)],
            Function.update μ' (y + posY n p c0 RBC c b) 1⟩ := by
    rintro _ rfl
    exact Ends.storeTo (y + posY n p c0 RBC c b) 1 ⟨_, rfl⟩
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, posY] <;> omega)))
  -- r := rbc[b n + c0 + c]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (r : ℕ) ?_ ?_ ?_);
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
  -- if r ≠ 0 then r := p - r
  refine Ends.next 8 (Ends.iteLast (fun h0 => Ends.skip (mark _ ?_)) fun h0 =>
    Ends.setTo (p - r : ℕ) (mark _ ?_))
  · have h0 : r = 0 := by simpa using h0
    rw [hlab, if_pos h0, h0]
  · have h0 : r ≠ 0 := by simpa using h0
    rw [hlab, if_neg h0]

open WriteY in
/-- The two loops of writeY are loops that mark cells. -/
theorem writeY_markCtx (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) :
    MarkCtx lim P d μ y (D * n) len n 32 (posY n p c0 RBC) C B (v LEN) (v N) writeYCell
      fun c b t => [y, rbc, n, D, p, c0, len, c, b, t, (D * n : ℕ)] where
  wordU := pre.len_le_word
  wordW := pre.n_le_word
  atU _ _ _ := rfl
  atW _ _ _ := rfl
  setU _ _ _ _ := rfl
  setW _ _ _ _ := rfl
  boundU _ _ _ _ := by simp
  boundW _ _ _ _ := by simp
  pos_lt _ _ hc hb := posY_lt pre hc hb
  cell_spec _ _ t _ hc hb hrest := writeYCell_spec pre t hc hb hrest

open WriteY in
/-- **writeY** writes the matrix Y and changes nothing else. -/
theorem writeY_spec (pre : WritePre lim μ y (D * n) rbc n D p c0 len RBC) :
    Ends lim P d writeYBody ⟨frame [y, rbc, n, D, p, c0, len], μ⟩ (tWriteY n D len) fun σ' =>
      Seg σ'.mem y (yList n D p c0 len RBC) ∧ SameOutside μ σ'.mem y (D * n) := by
  (obtain ⟨⟩ := id pre)
  unfold tWriteY
  -- sz := D n
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
          (D * n : ℕ)
            -- for c < sz: y[c] := 0
            
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
  -- for c < sz: y[c] := 0
  refine Ends.next _
    (clear_spec pre.hw pre.spaceM (by decide) (by decide) rfl rfl fun μ' hzero hrest => ?_)
  -- for c < len: for b < n: the pair (c, b) marks its cell
  refine ((markPairs (writeY_markCtx pre) _ _ _ (.start hzero hrest)).mono ?_ fun σ' hm =>
    ⟨hm.seg (by simp [yList]) fun i hi => getElem_yList ?_ hi, hm.rest⟩)
  · first
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
           | ((ring_nf); (omega)))
  · have hi' : i < D * n := by simpa [yList] using hi
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi'
    have hl : 0 < RBC.length := by rw [pre.length]; exact Nat.mul_pos hn hn
    have := pre.lt _ (List.getElem_mem hl)
    omega

end writeY

/-! ## The matrix X -/

namespace WriteX

















end WriteX


























/-- Entry i of xList, the matrix X row by row, is 1 if one of the pairs (a, c) marks the cell i, and
0 if not. -/
theorem getElem_xList {n D p c0 len rho : ℕ} {RAC : List ℕ} (hp : 0 < p) (hD : len * p ≤ D) {i : ℕ}
    (hi : i < (xList n D p c0 len rho RAC).length) :
    (xList n D p c0 len rho RAC)[i] = markVal (posX n D p c0 rho RAC) len n 0 i := by
  have hi' : i < n * D := by simpa [xList] using hi
  rw [markVal_end
    (i % D / p < len ∧ i % D % p = (RAC.getD (i / D * n + c0 + i % D / p) 0 + rho) % p)]
  · simp [xList]
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨i / D, Nat.div_lt_of_lt_mul' hi', i % D / p, h1, ?_⟩
      rw [posX, labX, ← h2, Nat.mul_comm (i % D / p) p, Nat.div_add_mod, Nat.mul_comm (i / D) D,
        Nat.div_add_mod]
    · rintro ⟨a, ha, c, hc, rfl⟩
      have hl : labX n p c0 rho RAC a c < p := Nat.mod_lt _ hp
      have hcol : c * p + labX n p c0 rho RAC a c < D := (Nat.mul_add_lt_mul hc hl).trans_le hD
      rw [posX, Nat.mul_add_div_of_lt hcol, Nat.mul_add_mod_of_lt hcol, Nat.mul_add_div_of_lt hl,
        Nat.mul_add_mod_of_lt hl]
      exact ⟨hc, rfl⟩

section writeX

variable {μ μ' : ℕ → ℤ} {x rac n D p c0 len rho : ℕ} {RAC : List ℕ}

/-- The cell of a pair lies in the matrix. -/
theorem posX_lt (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) {a c : ℕ} (ha : a < n)
    (hc : c < len) : posX n D p c0 rho RAC a c < n * D := by
  have hp := pre.getD_lt (pre.index_lt ha hc)
  exact Nat.mul_add_lt_mul ha (pre.middle_lt hc (Nat.mod_lt _ (by omega)))

/-- The label, as the program computes it. -/
theorem labX_eq {a c : ℕ} (hr : RAC.getD (a * n + c0 + c) 0 < p) (hrho : rho < p) :
    labX n p c0 rho RAC a c = if RAC.getD (a * n + c0 + c) 0 + rho < p
      then RAC.getD (a * n + c0 + c) 0 + rho else RAC.getD (a * n + c0 + c) 0 + rho - p := by
  unfold labX
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

open WriteX in
/-- **One pair of writeX.** -/
theorem writeXCell_spec (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) (hrho : rho < p)
    {a c : ℕ} (t : ℤ) (ha : a < n) (hc : c < len) (hrest : SameOutside μ μ' x (n * D)) :
    Ends lim P d writeXCell ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t, (n * D : ℕ)], μ'⟩ 34
      fun σ' => ∃ t', σ' = ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t', (n * D : ℕ)],
        Function.update μ' (x + posX n D p c0 rho RAC a c) 1⟩ := by
  (obtain ⟨⟩ := id pre)
  have hidx := pre.index_lt ha hc
  have hread := pre.read hrest hidx
  have hr := pre.getD_lt hidx
  have hlab := labX_eq hr hrho
  have hpos : a * D + (c * p + labX n p c0 rho RAC a c) < n * D := posX_lt pre ha hc
  have haddr : ((rac : ℤ) + a * n + c0 + c).toNat = rac + (a * n + c0 + c) := by omega
  generalize RAC.getD (a * n + c0 + c) 0 = r at hread hr hlab
  -- x[a D + c p + t] := 1, once t is the label
  have mark : ∀ s : ℕ, labX n p c0 rho RAC a c = s →
      Ends lim P d (.store (((Light.Expr.op Light.Op.add)
                              ((Light.Expr.op Light.Op.add)
                                ((Light.Expr.op Light.Op.add) (v X)
                                  ((Light.Expr.op Light.Op.mul) (v A) (v DD)))
                                ((Light.Expr.op Light.Op.mul) (v C) (v PR)))
                              (v T))) (k 1))
        ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, s, (n * D : ℕ)], μ'⟩ 13 fun σ' =>
          ∃ t', σ' = ⟨frame [x, rac, n, D, p, c0, len, rho, a, c, t', (n * D : ℕ)],
            Function.update μ' (x + posX n D p c0 rho RAC a c) 1⟩ := by
    rintro _ rfl
    exact Ends.storeTo (x + posX n D p c0 rho RAC a c) 1 ⟨_, rfl⟩ (by (((try have := Light.Std.space_le (by assumption)));
                                                                            ((try have := Light.Std.const_le (by assumption)));
                                                                            (simp [Light.Limits.Addr, abs_le, -abs_mul, posX] <;> omega)))
  -- t := rac[a n + c0 + c] + rho
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (r + rho : ℕ) ?_ ?_ ?_);
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
  -- if p ≤ t then t := t - p
  refine Ends.next 8 (Ends.iteLast (fun h0 => Ends.skip (mark _ ?_)) fun h0 => ?_)
  · have h0 : r + rho < p := by simp at h0; omega
    rw [hlab, if_pos h0]
  · have h0 : ¬ r + rho < p := by simp at h0; omega
    exact Ends.setTo (r + rho - p : ℕ) (mark _ (by rw [hlab, if_neg h0]))

open WriteX in
/-- The two loops of writeX are loops that mark cells. -/
theorem writeX_markCtx (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) (hrho : rho < p) :
    MarkCtx lim P d μ x (n * D) n len 34 (posX n D p c0 rho RAC) A C (v N) (v LEN) writeXCell
      fun a c t => [x, rac, n, D, p, c0, len, rho, a, c, t, (n * D : ℕ)] where
  wordU := pre.n_le_word
  wordW := pre.len_le_word
  atU _ _ _ := rfl
  atW _ _ _ := rfl
  setU _ _ _ _ := rfl
  setW _ _ _ _ := rfl
  boundU _ _ _ _ := by simp
  boundW _ _ _ _ := by simp
  pos_lt _ _ ha hc := posX_lt pre ha hc
  cell_spec _ _ t _ ha hc hrest := writeXCell_spec pre hrho t ha hc hrest

open WriteX in
/-- **writeX** writes the matrix X and changes nothing else. -/
theorem writeX_spec (pre : WritePre lim μ x (n * D) rac n D p c0 len RAC) (hrho : rho < p) :
    Ends lim P d writeXBody ⟨frame [x, rac, n, D, p, c0, len, rho], μ⟩ (tWriteX n D len) fun σ' =>
      Seg σ'.mem x (xList n D p c0 len rho RAC) ∧ SameOutside μ σ'.mem x (n * D) := by
  (obtain ⟨⟩ := id pre)
  unfold tWriteX
  -- sz := n D
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
          (n * D : ℕ)
            -- for a < sz: x[a] := 0
            
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
  -- for a < sz: x[a] := 0
  refine Ends.next _
    (clear_spec pre.hw pre.spaceM (by decide) (by decide) rfl rfl fun μ' hzero hrest => ?_)
  -- for a < n: for c < len: the pair (a, c) marks its cell
  refine ((markPairs (writeX_markCtx pre hrho) _ _ _ (.start hzero hrest)).mono ?_ fun σ' hm =>
    ⟨hm.seg (by simp [xList]) fun i hi => getElem_xList (by omega) pre.fits hi, hm.rest⟩)
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
        | ((ring_nf); (omega)))

end writeX

end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the loop over the instances

Proof of Theorem 17.  After the prime has been chosen and the query pairs have been sorted into
classes and cut into chunks, the host runs through all instances: instance number t belongs to the
piece number t / chunkCount of the third part of the vertices and to the chunk number t % chunkCount
of the table of chunks.  For each instance it writes the two biadjacency matrices, calls the solver
of Lop-AE-SparseTri on the chunk (a segment of the sorted arrays of query pairs, so nothing is
copied), and scans the piece for every accepted query pair, as long as no zero triangle has been
found.

The solver is arbitrary.  The facts about the data that the loop relies on are collected in the
structure `HostOk`.

* What the four calls assume is proved without any program: `HostSetting.writeX`,
  `HostSetting.writeY`, `HostSetting.solver`, `HostSetting.weights`, `HostSetting.answers`.
* The program has one lemma for each part of a round: `hostParams_spec` (the parameters of the
  instance), `hostCalls_spec` (the four calls) and `hostNext_spec` (the counters).
  `hostRound_spec` puts them together, and `hostLoop_spec` is the loop: hostLoop returns 1 if a scan
  has found a zero triangle (`X.found X.m`) and 0 if not, changes no cell below x, and takes at most
  `tHostLoop` steps, the sum over the instances of the times of the four calls.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedure -/

namespace HostLocal




























































end HostLocal

open HostLocal
















































/-! ## What the loop relies on -/



















































































/-! ## What the calls assume -/











/-- Entries 0 and 1 have absolute value at most 1. -/
private theorem absLe_one_of_zero_or_one {L : List ℤ} (h : ∀ e ∈ L, e = 0 ∨ e = 1) :
    AbsLe L ((1 : ℕ) : ℤ) := by
  intro e he
  rcases h e he with rfl | rfl <;> simp

namespace HostSetting

variable {X : HostData} {U : ℕ} {A : HostAddr} {need : List ℕ → Need} {μ μ' μ'' : ℕ → ℤ} {t : ℕ}

/-- The order of the regions of the memory, the limits, and the sizes of instance t. -/
theorem places (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    A.ab + X.n * X.n ≤ A.x ∧ A.bc + X.n * X.n ≤ A.x ∧ A.ac + X.n * X.n ≤ A.x ∧
      A.rac + X.n * X.n ≤ A.x ∧ A.rbc + X.n * X.n ≤ A.x ∧ A.qi + X.n * X.n ≤ A.x ∧
      A.qj + X.n * X.n ≤ A.x ∧ A.cr + X.chunkCount ≤ A.x ∧ A.cl + X.chunkCount ≤ A.x ∧
      A.cw + X.chunkCount ≤ A.x ∧ A.x + X.n * X.D ≤ A.y ∧ A.y + X.D * X.n ≤ A.out ∧
      A.out + X.w t ≤ A.fr ∧
      (lim.space : ℤ) ≤ lim.word ∧ A.fr < lim.space ∧ 2 * X.p < lim.space ∧
      (X.m : ℤ) ≤ lim.word ∧ ((X.n + X.q : ℕ) : ℤ) ≤ lim.word ∧ d + 2 ≤ lim.depth ∧
      X.c0 t + X.len t ≤ X.n ∧ X.lo t + X.w t ≤ X.n * X.n ∧ t % X.chunkCount < X.chunkCount :=
  ⟨S.lay.bAB, S.lay.bBC, S.lay.bAC, S.lay.bRAC, S.lay.bRBC, S.lay.bQI, S.lay.bQJ, S.lay.bCR,
    S.lay.bCL, S.lay.bCW, S.lay.xy, S.lay.yo, S.lay.ofr t ht, S.fits.space, S.fits.fr, S.fits.prime,
    S.fits.count, S.fits.step, S.fits.depth, S.ok.valid.piece_le ht, S.ok.valid.lo_add_le ht,
    HostData.mod_chunkCount_lt ht⟩

/-- A later memory that agrees with μ' below x. -/
theorem next (S : HostSetting lim d X U A need μ μ') (h : ∀ a < A.x, μ'' a = μ' a) :
    HostSetting lim d X U A need μ μ'' :=
  { S with kept := fun a ha => (h a ha).trans (S.kept a ha) }

/-- There are `n²` residues of the weights `w(a,c)`. -/
theorem length_RAC (S : HostSetting lim d X U A need μ μ') : X.RAC.length = X.n * X.n := by
  simp [HostData.RAC, residList, S.ok.valid.lenAC]

/-- There are `n²` residues of the weights `w(b,c)`. -/
theorem length_RBC (S : HostSetting lim d X U A need μ μ') : X.RBC.length = X.n * X.n := by
  simp [HostData.RBC, residList, S.ok.valid.lenBC]

/-- What the loop reads stands in μ' as it stood in μ. -/
theorem mem_prime (S : HostSetting lim d X U A need μ μ') : HostMem X A μ' := by
  ((obtain ⟨⟩ := id S); (obtain ⟨⟩ := id S.lay); (obtain ⟨⟩ := id S.ok.valid))
  have lenRAC := S.length_RAC
  have lenRBC := S.length_RBC
  have lenQI := S.ok.valid.length_QI
  have lenQJ := S.ok.valid.length_QJ
  have lenCT : X.CT.length = X.chunkCount := rfl
  have h := S.mem
  exact
    { segAB := h.segAB.keep
      segBC := h.segBC.keep
      segAC := h.segAC.keep
      segRAC := h.segRAC.keep
      segRBC := h.segRBC.keep
      segQI := h.segQI.keep
      segQJ := h.segQJ.keep
      segCR := h.segCR.keep
      segCL := h.segCL.keep
      segCW := h.segCW.keep }

/-- Reading an entry of a component of the table of chunks. -/
theorem read_tab {a : ℕ} (f : Chunk → ℕ) (h : SegN μ a (X.CT.map f)) {i : ℕ}
    (hi : i < X.chunkCount) : μ (a + i) = (f (X.CT.getD i ⟨0, 0, 0⟩) : ℤ) := by
  have hi' : i < X.CT.length := hi
  rw [h i (by simpa using hi'), List.getD_eq_getElem _ _ hi']
  simp

/-- The three parameters of the chunk of instance t, in the memory. -/
theorem read_chunk (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    μ' (A.cr + t % X.chunkCount) = X.rho t ∧ μ' (A.cl + t % X.chunkCount) = X.lo t ∧
      μ' (A.cw + t % X.chunkCount) = X.w t :=
  ⟨read_tab (fun c => c.residue) S.mem_prime.segCR (HostData.mod_chunkCount_lt ht),
    read_tab (fun c => c.start) S.mem_prime.segCL (HostData.mod_chunkCount_lt ht),
    read_tab (fun c => c.len) S.mem_prime.segCW (HostData.mod_chunkCount_lt ht)⟩

/-- What writeX and writeY assume, for a matrix of size cells at dst and the residues of a list of
weights at r. -/
private theorem write (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) {dst size r : ℕ}
    {weights : List ℤ} (seg : SegN μ' r (residList X.p weights))
    (length : (residList X.p weights).length = X.n * X.n) (hsize : size = X.D * X.n)
    (hdst : dst + size < lim.space) (hr : r + X.n * X.n ≤ dst) :
    WritePre lim μ' dst size r X.n X.D X.p (X.c0 t) (X.len t) (residList X.p weights) where
  hw := S.fits.space
  seg := seg
  length := length
  lt := fun x hx => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
    exact resid_lt S.ok.valid.p_ne z
  fits := S.ok.valid.len_mul_le t
  piece := S.ok.valid.piece_le ht
  size := hsize
  spaceM := hdst
  spaceR := by omega
  spaceP := S.fits.prime
  apart := Or.inr hr

/-- The precondition of writeX holds. -/
theorem writeX (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    WritePre lim μ' A.x (X.n * X.D) A.rac X.n X.D X.p (X.c0 t) (X.len t) X.RAC := by
  have hplaces := S.places ht
  exact S.write ht S.mem_prime.segRAC S.length_RAC (Nat.mul_comm _ _) (by omega) (by omega)

/-- The precondition of writeY holds. -/
theorem writeY (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    WritePre lim μ' A.y (X.D * X.n) A.rbc X.n X.D X.p (X.c0 t) (X.len t) X.RBC := by
  have hplaces := S.places ht
  exact S.write ht S.mem_prime.segRBC S.length_RBC rfl (by omega) (by omega)






/-- The precondition of the solver holds, once the two matrices are written. -/
theorem solver (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) : lopDetectTask.Pre (inst X A t) μ' A.fr := by
  have hplaces := S.places ht
  have hv := S.ok.valid
  refine ⟨?_, ⟨X.matX_zero_or_one t, X.matY_zero_or_one t⟩, rfl⟩
  exact
    { N_pos := hv.n_pos
      D_pos := le_trans (Nat.mul_pos hv.q_pos hv.p_pos) hv.qp_le
      U_pos := le_rfl
      lenX := X.length_matX t
      lenY := X.length_matY t
      lenWI := hv.length_WI ht
      lenWJ := hv.length_WJ ht
      segX := hX
      segY := hY
      segWI := SegN.drop_take S.mem_prime.segQI _ _
      segWJ := SegN.drop_take S.mem_prime.segQJ _ _
      leX := absLe_one_of_zero_or_one (X.matX_zero_or_one t)
      leY := absLe_one_of_zero_or_one (X.matY_zero_or_one t)
      ltWI := fun _ => HostData.lt_of_mem_WI
      ltWJ := fun _ => HostData.lt_of_mem_WJ
      nodup := X.nodup_zip t
      belowX := by simp only [inst]; omega
      belowY := by simp only [inst]; omega
      belowWI := by simp only [inst]; omega
      belowWJ := by simp only [inst]; omega
      belowOut := by simp only [inst]; omega
      apartX := by simp only [inst]; omega
      apartY := by simp only [inst]; omega
      apartWI := by simp only [inst]; omega
      apartWJ := by simp only [inst]; omega }

/-- The weights are where the scans read them. -/
theorem weights (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Weights lim μ' A.ab A.bc A.ac X.n U X.AB X.BC X.AC := by
  have hplaces := S.places ht
  have hm := S.mem_prime
  have hv := S.ok.valid
  exact
    { hw := S.fits.space
      hU := by exact_mod_cast S.fits.weights
      arrAB := { len := hv.lenAB, seg := hm.segAB, bound := S.ok.leAB }
      arrBC := { len := hv.lenBC, seg := hm.segBC, bound := S.ok.leBC }
      arrAC := { len := hv.lenAC, seg := hm.segAC, bound := S.ok.leAC } }

/-- The answers of the solver and the query pairs of the chunk are where the scans read them. -/
theorem answers (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (hans : Seg μ' A.out (X.ans t)) :
    Answers lim μ' A.out (A.qi + X.lo t) (A.qj + X.lo t) (X.w t) X.n (X.ans t) (X.WI t)
      (X.WJ t) := by
  have hplaces := S.places ht
  have hv := S.ok.valid
  exact
    { arrOUT :=
        { len := by simp [HostData.ans, thinOut, hv.length_WI ht, hv.length_WJ ht], seg := hans }
      arrQA :=
        { len := hv.length_WI ht, seg := SegN.drop_take S.mem_prime.segQI _ _
          lt := fun _ => HostData.lt_of_mem_WI }
      arrQB :=
        { len := hv.length_WJ ht, seg := SegN.drop_take S.mem_prime.segQJ _ _
          lt := fun _ => HostData.lt_of_mem_WJ }
      w_lt := by omega }

end HostSetting

/-! ## The parts of a round -/

variable {P₀ R : Program} {pS pWriteX pWriteY pScanPairs pScan : ℕ} {Tn : List ℕ → ℕ}
  {need : List ℕ → Need} {X : HostData} {U : ℕ} {A : HostAddr} {μ μ' : ℕ → ℤ} {t : ℕ}








/-- **The parameters of instance t.** -/
theorem hostParams_spec {P : Program} (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (fnd len rho lo w res : ℤ) :
    Ends lim P d hostParams (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 27
      (· = hostState X A t (t % X.chunkCount) (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res
        μ') := by
  have hplaces := S.places ht
  obtain ⟨hrho, hlo, hw⟩ := S.read_chunk ht
  have hlen : X.len t = min X.q (X.n - X.c0 t) := rfl
  generalize t % X.chunkCount = ch at *
  -- rho := mem[cr + ch]; lo := mem[cl + ch]; w := mem[cw + ch]
  have htail : ∀ len' : ℤ, len' = X.len t → Ends lim P d
      ((Light.Stmt.seq
         (.set Residue (M ((Light.Expr.op Light.Op.add) (v TabR) (v ChunkNo))))
         (Light.Stmt.seq
           (.set Start (M ((Light.Expr.op Light.Op.add) (v TabL) (v ChunkNo))))
           (.set NumPairs (M ((Light.Expr.op Light.Op.add) (v TabW) (v ChunkNo)))))))
      (hostState X A t ch (X.c0 t) fnd len' rho lo w res μ') 15
      (· = hostState X A t ch (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res μ') := by
    rintro _ rfl
    refine Ends.setToThen (X.rho t : ℤ) ?_ (by (((try have := Light.Std.space_le (by assumption)));
                                                   ((try have := Light.Std.const_le (by assumption)));
                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, hrho] <;> omega)))
    refine Ends.setToThen (X.lo t : ℤ) ?_ (by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, hlo] <;> omega)))
    exact Ends.setTo (X.w t : ℤ) rfl (by (((try have := Light.Std.space_le (by assumption)));
                                             ((try have := Light.Std.const_le (by assumption)));
                                             (simp [Light.Limits.Addr, abs_le, -abs_mul, hw] <;> omega)))
  unfold hostParams
  -- len := q
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen X.q ?_ ?_ ?_);
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
  -- if n - c0 < q then len := n - c0
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · replace hc : (X.n : ℤ) - X.c0 t < X.q := by simpa using hc
    exact Ends.setToThen (X.len t : ℤ) ((htail _ rfl).mono (by first
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
                                                                       | ((ring_nf); (omega)))) fun _ h => h)
  · replace hc : ¬ (X.n : ℤ) - X.c0 t < X.q := by simpa using hc
    refine Ends.next 0 (Ends.skip ?_)
    exact (htail _ (by omega)).mono (by first
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
                                              | ((ring_nf); (omega)))) fun _ h => h






/-- The call of writeX for instance t. -/
theorem HostCtx.writeX_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Meets lim (P₀ ++ R) pWriteX (d + 1)
      [(A.x : ℤ), A.rac, X.n, X.D, X.p, X.c0 t, X.len t, X.rho t] μ' (tWriteX X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.x (X.matX t) ∧ SameOutside μ' μ₁ A.x (X.n * X.D) :=
  Meets.of_body C.writeX (writeX_spec (S.writeX ht) (S.ok.valid.rho_lt ht))

/-- The call of writeY for instance t. -/
theorem HostCtx.writeY_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Meets lim (P₀ ++ R) pWriteY (d + 1) [(A.y : ℤ), A.rbc, X.n, X.D, X.p, X.c0 t, X.len t] μ'
      (tWriteY X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.y (X.matY t) ∧ SameOutside μ' μ₁ A.y (X.D * X.n) :=
  Meets.of_body C.writeY (writeY_spec (S.writeY ht))

/-- The call of the solver for instance t, once the two matrices are written. -/
theorem HostCtx.solver_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) :
    Meets lim (P₀ ++ R) pS (d + 1)
      [(X.n : ℤ), X.D, X.w t, (1 : ℕ), A.x, A.y, (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), A.out,
        A.fr] μ' (Tn [X.n, X.D, X.w t])
      fun _ μ₁ => Seg μ₁ A.out (X.ans t) ∧ KeptBut μ' μ₁ A.fr A.out (X.w t) :=
  C.sol.meets R (HostSetting.inst X A t) (S.solver ht hX hY) (S.fits.solver t ht)

/-- The call of scanPairs for instance t, once the solver has answered. -/
theorem HostCtx.scanPairs_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hans : Seg μ' A.out (X.ans t)) :
    Meets lim (P₀ ++ R) pScanPairs (d + 1)
      [(A.out : ℤ), (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), X.w t, bit (X.found t), A.ab, A.bc,
        A.ac, X.n, X.c0 t, X.len t] μ' (tScanPairs (X.w t) (X.len t) (X.execs t))
      fun r μ₁ => r = bit (X.found (t + 1)) ∧ μ₁ = μ' := by
  have hplaces := S.places ht
  exact Meets.of_body C.scanPairs (scanPairs_spec (f := X.found t) C.scan (S.weights ht)
    (S.answers ht hans) (by omega) (S.ok.valid.piece_le ht))

/-- **The four calls for instance t.** -/
theorem hostCalls_spec (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (ch : ℕ) (res : ℤ) :
    Ends lim (P₀ ++ R) d (hostCalls pS pWriteX pWriteY pScanPairs)
      (hostState X A t ch (X.c0 t) (bit (X.found t)) (X.len t) (X.rho t) (X.lo t) (X.w t) res μ')
      (tCalls Tn X t) fun σ => ∃ (res' : ℤ) (μ'' : ℕ → ℤ),
        σ = hostState X A t ch (X.c0 t) (bit (X.found (t + 1))) (X.len t) (X.rho t) (X.lo t)
          (X.w t) res' μ'' ∧ HostSetting lim d X U A need μ μ'' := by
  have hplaces := S.places ht
  unfold hostCalls tCalls
  -- res := writeX(x, rac, n, D, p, c0, len, rho)
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
          Light.Ends.callToThen ((C.writeX_meets S ht) _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen (C.writeX_meets S ht) ?_ ?_ ?_ ?_);
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
        ((rintro r₁ μ₁ ⟨hX, hrest₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have S₁ := S.next fun a ha => hrest₁ a (Or.inl ha)
  -- res := writeY(y, rbc, n, D, p, c0, len)
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
          Light.Ends.callToThen ((C.writeY_meets S₁ ht) _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen (C.writeY_meets S₁ ht) ?_ ?_ ?_ ?_);
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
        ((rintro r₂ μ₂ ⟨hY, hrest₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have S₂ := S₁.next fun a ha => hrest₂ a (Or.inl (by omega))
  replace hX : Seg μ₂ A.x (X.matX t) :=
    hX.keep (by ((try have := X.length_matX t);
                  (((try refine Light.SameOn.cell ?_);
                      (intro apspMacro_203996_0 apspMacro_203996_1);
                      (first
                        |
                          ((((repeat
                                    (((with_reducible
                                            rename Light.SameOn _ _ _ => apspMacro_203996_2));
                                      ((try
                                            have :=
                                              apspMacro_203996_2 apspMacro_203996_0
                                                (by omega)));
                                      (revert apspMacro_203996_2)));
                                (intros);
                                (try simp only [Function.update_apply, Light.wrote] at *)));
                            (omega))
                        |
                          ((simp [X.length_matX t] at apspMacro_203996_1);
                            (((repeat
                                    (((with_reducible
                                            rename Light.SameOn _ _ _ => apspMacro_203996_3));
                                      ((try
                                            have :=
                                              apspMacro_203996_3 apspMacro_203996_0
                                                (by omega)));
                                      (revert apspMacro_203996_3)));
                                (intros);
                                (try simp only [Function.update_apply, Light.wrote] at *)));
                            (omega))
                        |
                          ((((repeat
                                    (((with_reducible
                                            rename Light.SameOn _ _ _ => apspMacro_203996_4));
                                      ((try
                                            have :=
                                              apspMacro_203996_4 apspMacro_203996_0
                                                (by omega)));
                                      (revert apspMacro_203996_4)));
                                (intros);
                                (try simp only [Function.update_apply, Light.wrote] at *)));
                            (fail
                                "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                          its condition K x does not follow from the hypotheses.")))))))
  -- res := solver(n, D, w, 1, x, y, qi + lo, qj + lo, out, fr)
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
          Light.Ends.callToThen ((C.solver_meets S₂ ht hX hY) _ (by omega)) ?_ ?_
            ?_ ?_
      | refine Light.Ends.callToThen (C.solver_meets S₂ ht hX hY) ?_ ?_ ?_ ?_);
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
        ((rintro r₃ μ₃ ⟨hans, hkept₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have S₃ := S₂.next fun a ha => hkept₃ a (by omega)
  -- fnd := scanPairs(out, qi + lo, qj + lo, w, fnd, ab, bc, ac, n, c0, len)
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
          Light.Ends.callToThen ((C.scanPairs_meets S₃ ht hans) _ (by omega)) ?_
            ?_ ?_ ?_
      | refine Light.Ends.callToThen (C.scanPairs_meets S₃ ht hans) ?_ ?_ ?_ ?_);
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
        ((rintro _ μ₄ ⟨rfl, rfl⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨r₃, μ₄, rfl, S₃⟩

/-- **The counters**: from instance t to instance t + 1. -/
theorem hostNext_spec {P : Program} (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (fnd len rho lo w res : ℤ) :
    Ends lim P d hostNext (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 18
      (· = hostState X A (t + 1) ((t + 1) % X.chunkCount) (X.c0 (t + 1)) fnd len rho lo w res
        μ') := by
  have hplaces := S.places ht
  have hlast := Nat.succ_div_mod_of_eq (n := X.chunkCount) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (n := X.chunkCount) (i := t) (by omega)
  have hc0 : X.c0 t = t / X.chunkCount * X.q := rfl
  have hc0' : X.c0 (t + 1) = (t + 1) / X.chunkCount * X.q := rfl
  generalize t % X.chunkCount = ch at *
  generalize (t + 1) % X.chunkCount = ch' at *
  -- t := t + 1
  have htail : Ends lim P d (.set Inst (((Light.Expr.op Light.Op.add) (v Inst) (k 1))))
      (hostState X A t ch' (X.c0 (t + 1)) fnd len rho lo w res μ') 4
      (· = hostState X A (t + 1) ch' (X.c0 (t + 1)) fnd len rho lo w res μ') :=
    Ends.setTo (t + 1 : ℕ) rfl
  unfold hostNext
  -- ch := ch + 1
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
          (ch + 1 : ℕ)
            -- if ch = chunkCount
            
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
  -- if ch = chunkCount
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · replace hc : ch + 1 = X.chunkCount := by
      have : ((ch + 1 : ℕ) : ℤ) = X.chunkCount := by simpa using hc
      exact_mod_cast this
    obtain ⟨hdiv, rfl⟩ := hlast hc
    have hstep : X.c0 (t + 1) = X.c0 t + X.q := by rw [hc0', hc0, hdiv, Nat.succ_mul]
    -- ch := 0; c0 := c0 + q
    have hwrap : Ends lim P d ((Light.Stmt.seq (.set ChunkNo (k 0))
                                 (.set PieceStart ((Light.Expr.op Light.Op.add) (v PieceStart) (v PieceLen)))))
        (hostState X A t (ch + 1) (X.c0 t) fnd len rho lo w res μ') 6
        (· = hostState X A t 0 (X.c0 (t + 1)) fnd len rho lo w res μ') :=
      Ends.setToThen ((0 : ℕ) : ℤ)
        (Ends.setTo (X.c0 (t + 1) : ℕ) rfl (by (((try have := Light.Std.space_le (by assumption)));
                                                   ((try have := Light.Std.const_le (by assumption)));
                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, hstep] <;> omega))))
    refine Ends.next _ (hwrap.mono le_rfl ?_)
    rintro _ rfl
    exact htail.mono (by first
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
                               | ((ring_nf); (omega)))) fun _ h => h
  · replace hc : ch + 1 ≠ X.chunkCount := fun h => hc (by simp; exact_mod_cast h)
    obtain ⟨hdiv, rfl⟩ := hinner hc
    have hstep : X.c0 (t + 1) = X.c0 t := by rw [hc0', hc0, hdiv]
    -- skip
    refine Ends.next 0 (Ends.skip ?_)
    rw [← hstep]
    exact htail.mono (by first
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
                               | ((ring_nf); (omega)))) fun _ h => h

/-! ## The loop -/








/-- **One round of the loop.** -/
theorem hostRound_spec (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (ht : t < X.m) {σ : State} (hσ : HostInv lim d X U A need μ t σ) :
    Ends lim (P₀ ++ R) d (hostRound pS pWriteX pWriteY pScanPairs) σ (tCalls Tn X t + 45)
      (HostInv lim d X U A need μ (t + 1)) := by
  obtain ⟨len, rho, lo, w, res, μ', rfl, S⟩ := hσ
  unfold hostRound
  -- the parameters of the instance
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      |
        refine
          Light.Ends.pieceThen (hostParams_spec S ht _ len rho lo w res) ?_ ?_
      |
        refine
          Light.Ends.pieceLast (hostParams_spec S ht _ len rho lo w res) ?_ ?_);
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
  -- the four calls
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (hostCalls_spec C S ht _ res) ?_ ?_
      | refine Light.Ends.pieceLast (hostCalls_spec C S ht _ res) ?_ ?_);
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
          ⟨res', μ'', rfl, S'⟩
              -- the counters
              )
  -- the counters
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (hostNext_spec S' ht _ _ _ _ _ res') ?_ ?_
      | refine Light.Ends.pieceLast (hostNext_spec S' ht _ _ _ _ _ res') ?_ ?_);
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
  exact ⟨_, _, _, _, _, μ'', rfl, S'⟩

/-- **hostLoop** returns 1 if a scan has found a zero triangle, and 0 if not, and changes no cell
below x. -/
theorem hostLoop_spec (C : HostCtx P₀ R pS pWriteX pWriteY pScanPairs pScan Tn need)
    (hok : HostOk X U) (hmem : HostMem X A μ) (hlay : HostLay X A)
    (hlim : HostLim lim d X U A need) :
    Ends lim (P₀ ++ R) d (hostLoopBody pS pWriteX pWriteY pScanPairs)
      ⟨frame (hostLoopArgs X A), μ⟩ (tHostLoop Tn X) fun σ' =>
      σ'.loc 0 = bit (X.found X.m) ∧ Kept μ σ'.mem A.x := by
  have hw := hlim.space
  have hT : ∑ t ∈ Finset.range X.m, (4 + (tCalls Tn X t + 45))
      ≤ ∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
        tScanPairs (X.w t) (X.len t) (X.execs t)) :=
    Finset.sum_le_sum fun t _ => by simp [tCalls, tWrites]; omega
  unfold hostLoopBody tHostLoop hostLoopArgs
  -- t := 0; ch := 0; c0 := 0; fnd := 0
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
            -- while t < m
            
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
  -- while t < m
  refine Ends.next _ (Ends.while (HostInv lim d X U A need μ) X.m (fun t => tCalls Tn X t + 45)
    ?start ?round ?done) (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)
  case start =>
    refine ⟨0, 0, 0, 0, 0, μ, ?_, hok, hmem, hlay, hlim, fun _ _ => rfl⟩
    rw [hostState, ← frame_append_zeros _ 5]
    simp [HostData.c0, HostData.found, bit]
  case round =>
    intro t σ ht hσ
    obtain ⟨len, rho, lo, w, res, μ', rfl, -⟩ := id hσ
    exact ⟨⟨trivial, trivial⟩, by simpa using ht, hostRound_spec C ht hσ⟩
  case done =>
    rintro _ ⟨len, rho, lo, w, res, μ', rfl, S⟩
    -- return fnd
    exact ⟨⟨trivial, trivial⟩, by simp, Ends.setTo (bit (X.found X.m)) ⟨by simp, S.kept⟩
      (hT := by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)⟩

end Light.Sec3

end
end

section


/-!
# The pure side of counting sort

`N` items `0, …, N - 1` have keys `kf 0, …, kf (N - 1)`.  A stable sort by key puts item `j` at the
place `sortPos kf N j`: the number of items with a smaller key plus the number of earlier items with
the same key.

This is a bijection of `{0, …, N - 1}` (`eq_of_sortPos_eq`, `exists_sortPos_eq`) that is increasing
for the order "smaller key, or same key and earlier" (`sortPos_lt_sortPos_iff`).
-/

@[expose] public section

namespace ThreeSumApsp










section
variable (kf : ℕ → ℕ)





@[simp] theorem cntLt_zero_left (j : ℕ) : cntLt kf 0 j = 0 := by simp [cntLt]

/-- One more item: it is counted if its key is `t`. -/
theorem cntEq_succ (t j : ℕ) : cntEq kf t (j + 1) = cntEq kf t j + if kf j = t then 1 else 0 :=
  Nat.count_succ _ _

/-- One more item: it is counted if its key is below `t`. -/
theorem cntLt_succ_right (t j : ℕ) :
    cntLt kf t (j + 1) = cntLt kf t j + if kf j < t then 1 else 0 := Nat.count_succ _ _

/-- Keys below `t + 1` are keys below `t` or equal to `t`. -/
theorem cntLt_succ_left (t j : ℕ) : cntLt kf (t + 1) j = cntLt kf t j + cntEq kf t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [cntLt_succ_right, cntLt_succ_right, cntEq_succ, ih]
    split_ifs <;> omega

/-- A larger bound counts more keys. -/
theorem cntLt_mono_left {s t : ℕ} (h : s ≤ t) (j : ℕ) : cntLt kf s j ≤ cntLt kf t j :=
  Nat.count_mono_left fun _ _ hlt => hlt.trans_le h

/-- At most all items are counted. -/
theorem cntLt_le (t j : ℕ) : cntLt kf t j ≤ j := Nat.count_le _

end

variable {kf : ℕ → ℕ} {N K : ℕ}







/-- If all keys are below `K`, all items are counted. -/
theorem cntLt_of_forall_lt (h : ∀ i < N, kf i < K) : cntLt kf K N = N :=
  Nat.count_iff_forall.mpr h

/-- Item `j` is itself one of the `N` items with its key. -/
theorem cntEq_lt_of_lt {j : ℕ} (hj : j < N) : cntEq kf (kf j) j < cntEq kf (kf j) N :=
  Nat.count_strict_mono (p := fun i => kf i = kf j) rfl hj

/-- The place of an item lies before the places of the larger keys. -/
theorem sortPos_lt_cntLt_succ {j : ℕ} (hj : j < N) : sortPos kf N j < cntLt kf (kf j + 1) N := by
  rw [cntLt_succ_left, sortPos]
  exact Nat.add_lt_add_left (cntEq_lt_of_lt hj) _

/-- The places are below `N`. -/
theorem sortPos_lt (kf : ℕ → ℕ) {j : ℕ} (hj : j < N) : sortPos kf N j < N :=
  calc sortPos kf N j < cntLt kf (kf j + 1) N := sortPos_lt_cntLt_succ hj
    _ ≤ N := cntLt_le ..

/-- A smaller key comes first; among equal keys the earlier item comes first. -/
theorem sortPos_lt_sortPos {i j : ℕ} (hi : i < N) (h : kf i < kf j ∨ (kf i = kf j ∧ i < j)) :
    sortPos kf N i < sortPos kf N j := by
  rcases h with hlt | ⟨heq, hij⟩
  · calc sortPos kf N i < cntLt kf (kf i + 1) N := sortPos_lt_cntLt_succ hi
      _ ≤ cntLt kf (kf j) N := cntLt_mono_left kf hlt N
      _ ≤ sortPos kf N j := Nat.le_add_right ..
  · rw [sortPos, sortPos, heq]
    exact Nat.add_lt_add_left (heq ▸ cntEq_lt_of_lt hij) _

/-- The order of the places is the order "smaller key, or same key and earlier". -/
theorem sortPos_lt_sortPos_iff {i j : ℕ} (hi : i < N) (hj : j < N) :
    sortPos kf N i < sortPos kf N j ↔ kf i < kf j ∨ (kf i = kf j ∧ i < j) := by
  refine ⟨fun h => ?_, sortPos_lt_sortPos hi⟩
  by_contra hc
  rcases (by omega : i = j ∨ kf j < kf i ∨ (kf j = kf i ∧ j < i)) with rfl | h'
  · omega
  · have := sortPos_lt_sortPos hj h'
    omega

/-- Different items get different places. -/
theorem eq_of_sortPos_eq {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : sortPos kf N i = sortPos kf N j) : i = j := by
  have hij := sortPos_lt_sortPos_iff (kf := kf) hi hj
  have hji := sortPos_lt_sortPos_iff (kf := kf) hj hi
  omega

/-- Every place is taken. -/
theorem exists_sortPos_eq (kf : ℕ → ℕ) {q : ℕ} (hq : q < N) : ∃ j < N, sortPos kf N j = q := by
  have hsurj := Finset.surjOn_of_injOn_of_card_le (s := Finset.range N) (t := Finset.range N)
    (sortPos kf N) (fun j hj => by simpa using sortPos_lt kf (by simpa using hj))
    (fun i hi j hj => eq_of_sortPos_eq (by simpa using hi) (by simpa using hj)) le_rfl
  simpa using hsurj (by simpa using hq)

end ThreeSumApsp

end
end

section


/-!
# The classes W_ϱ of the pairs (proof of Theorem 17)

"For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod p)".  (The cutting of
the classes into chunks, with which the sentence goes on, is a routine of its own.)

classes(rab, n, p, cls, cur, qi, qj) sorts the n² pairs (a, b) by the residue of w(a,b), which is in
the cell rab + a n + b, keeping the row-major order within a class: a stable counting sort.  It
writes the rows of the sorted pairs to qi, their columns to qj, and the places where the classes
start to cls.  The row and the column of the current pair are kept in two counters, so that no
division is needed.  `classes_meets` proves this, within `tClasses n p` steps, a number linear in
n² + p.

The routine has five phases.  Between them the state is described by `ClsState`:

* `clsZero_ends`: the counters are cleared;
* `clsCount_ends`: the sizes of the classes are counted;
* `clsPrefix_ends`: prefix sums turn the sizes into the starts;
* `clsCopy_ends`: the starts are copied to cur, the next free places;
* `clsPlace_ends`: each pair goes to the next free place of its class (`ClsPlaced.step` for the
  memory, `clsPlaceOne_ends` for the program), and row and column step to the next pair.

The place of a pair is its place `sortPos` in a stable sort; `getD_sortedIdx` and
`segN_map_sortedIdx` identify what stands there with the lists of the specification.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side: the lists of the specification and the places of a stable sort -/

section pure




/-- The size of a class, as a count of keys. -/
theorem length_classIdx (n : ℕ) (RAB : List ℕ) (r : ℕ) :
    (classIdx n RAB r).length = cntEq (clsKey RAB) r (n * n) :=
  List.length_filter_range (fun i => RAB.getD i 0 = r) (n * n)

/-- The sizes of the classes before `r` add up to the number of smaller keys. -/
theorem sum_length_classIdx (n : ℕ) (RAB : List ℕ) (r : ℕ) :
    ((List.range r).map fun r' => (classIdx n RAB r').length).sum =
      cntLt (clsKey RAB) r (n * n) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, cntLt_succ_left]
    simp [length_classIdx]

/-- An entry of the list of the starts. -/
theorem getD_classStarts (n p : ℕ) (RAB : List ℕ) {r : ℕ} (hr : r ≤ p) :
    (classStarts n p RAB).getD r 0 = cntLt (clsKey RAB) r (n * n) := by
  have h : r < p + 1 := by omega
  simp [classStarts, classStart, List.getD_eq_getElem?_getD, h, sum_length_classIdx]

/-- The pair number i stands at its place in the list of all the pairs, class after class. -/
theorem getD_sortedIdx (n p : ℕ) (RAB : List ℕ) {i : ℕ} (hi : i < n * n) (hk : clsKey RAB i < p) :
    (sortedIdx n p RAB).getD (sortPos (clsKey RAB) (n * n) i) 0 = i := by
  have ho : cntEq (clsKey RAB) (clsKey RAB i) i < (classIdx n RAB (clsKey RAB i)).length := by
    rw [length_classIdx]
    exact cntEq_lt_of_lt hi
  rw [sortedIdx, sortPos, ← sum_length_classIdx, List.getD_flatMap_range_sum _ hk ho]
  exact List.getD_filter_range_count (fun j => RAB.getD j 0 = clsKey RAB i) (n * n) hi rfl

/-- All the pairs are listed if all the keys are below `p`. -/
theorem length_sortedIdx (n p : ℕ) (RAB : List ℕ) (h : ∀ i < n * n, clsKey RAB i < p) :
    (sortedIdx n p RAB).length = n * n := by
  rw [sortedIdx, List.length_flatMap, sum_length_classIdx, cntLt_of_forall_lt h]

/-- What stands at the places of a stable sort is the list of the pairs, class after class. -/
theorem segN_map_sortedIdx {μ' : ℕ → ℤ} {n p : ℕ} {RAB : List ℕ}
    (hkeys : ∀ j < n * n, clsKey RAB j < p) {base : ℕ} (f : ℕ → ℕ)
    (h : ∀ j < n * n, μ' (base + sortPos (clsKey RAB) (n * n) j) = (f j : ℕ)) :
    SegN μ' base ((sortedIdx n p RAB).map f) := by
  have hlen := length_sortedIdx n p RAB hkeys
  intro q hq
  have hq' : q < n * n := by simpa [hlen] using hq
  obtain ⟨j, hj, rfl⟩ := exists_sortPos_eq (clsKey RAB) hq'
  have hg := getD_sortedIdx n p RAB hj (hkeys j hj)
  rw [List.getD_eq_getElem _ 0 (by rw [hlen]; exact hq')] at hg
  simp only [List.getElem_map, hg]
  exact h j hj

end pure

/-! ## The routine -/

namespace Classes




























end Classes










































































section phases

variable {μ μ' : ℕ → ℤ} {x : ClassesArgs}

/-- The keys are below p. -/
theorem ClassesPre.key_lt (pre : ClassesPre lim μ x) {i : ℕ} (hi : i < x.n * x.n) :
    clsKey x.RAB i < x.p := by
  have hl : i < x.RAB.length := pre.len ▸ hi
  rw [clsKey, List.getD_eq_getElem _ 0 hl]
  exact pre.lt _ (List.getElem_mem hl)

/-- The residues lie before the areas that are written, so they can be read at any time. -/
theorem ClassesPre.read (pre : ClassesPre lim μ x) (h : x.Same μ μ') {i : ℕ}
    (hi : i < x.n * x.n) : μ' (x.rab + i) = (clsKey x.RAB i : ℕ) := by
  have hl : i < x.RAB.length := pre.len ▸ hi
  have := pre.rab_le
  rw [h _ (by omega), pre.seg _ (by simpa using hl), List.getElem_map, clsKey,
    List.getD_eq_getElem _ 0 hl]


















variable {σ : State} (hw : (lim.space : ℤ) ≤ lim.word)

include hw

/-- cls[t] := 0 for t ≤ p. -/
theorem clsZero_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (fun _ => True) σ) :
    Ends lim P d clsZero σ (15 * x.p + 23) (ClsState μ x (ClsZeroed x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, -⟩ := h
  (obtain ⟨⟩ := id pre)
  refine Ends.forFrame
    (fun j μ'' => x.Same μ μ'' ∧ ∀ t < j, μ'' (x.cls + t) = 0) (x.p + 1)
    ⟨hrest, fun t ht => absurd ht (by omega)⟩ ?round ?done
  case round =>
    rintro j μ'' hj ⟨hr, hz⟩
    refine Ends.storeTo (x.cls + j) 0 ⟨rfl, hr.update ⟨by omega, by omega⟩ _, fun t ht => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (hz t ht)
    · exact Function.update_self ..
  case done =>
    exact fun μ'' ⟨hr, hz⟩ => ⟨_, ad, row, col, pl, μ'', rfl, hr, fun t ht => hz t (by omega)⟩

/-- cls[rab[i] + 1] += 1 for i < n². -/
theorem clsCount_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsZeroed x) σ) :
    Ends lim P d clsCount σ (23 * (x.n * x.n) + 6) (ClsState μ x (ClsCounted x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hz⟩ := h
  (obtain ⟨⟩ := id pre)
  refine Ends.for (fun j σ => ∃ (ad : ℤ) (μ'' : ℕ → ℤ),
      σ = ⟨frame (x.locals j ad row col pl), μ''⟩ ∧ x.Same μ μ'' ∧ μ'' x.cls = 0 ∧
      ∀ t < x.p, μ'' (x.cls + (t + 1)) = (cntEq (clsKey x.RAB) t j : ℕ)) (x.n * x.n) 15
    ?start ?round ?done ?bound
  case start =>
    exact ⟨ad, μ', by rw [update_frame_setLocal]; rfl, hrest, hz 0 (by omega),
      fun t ht => by simpa [cntEq] using hz (t + 1) (by omega)⟩
  case bound =>
    rintro j _ - - ⟨ad, μ'', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨ad, μ'', rfl, hr, hfirst, hc⟩
    exact ⟨_, ad, row, col, pl, μ'', rfl, hr, hfirst, hc⟩
  case round =>
    rintro j _ hj - ⟨ad, μ'', rfl, hr, hfirst, hc⟩
    have hread := pre.read hr hj
    have hk := pre.key_lt hj
    have hcell := hc _ hk
    have hle : cntEq (clsKey x.RAB) (clsKey x.RAB j) j ≤ j := Nat.count_le _
    have haddr :
        ((x.cls : ℤ) + ((clsKey x.RAB j : ℤ) + 1)).toNat = x.cls + (clsKey x.RAB j + 1) := by
      omega
    -- ad := cls + rab[i] + 1
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (x.cls + (clsKey x.RAB j + 1) : ℕ) ?_ ?_ ?_);
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
    -- mem[ad] := mem[ad] + 1
    refine Ends.storeTo (x.cls + (clsKey x.RAB j + 1))
      (cntEq (clsKey x.RAB) (clsKey x.RAB j) j + 1 : ℕ)
      ⟨by simp, _, _, by rw [update_frame_setLocal]; rfl, hr.update ⟨by omega, by omega⟩ _,
        (Function.update_of_ne (by omega) _ _).trans hfirst, fun t ht => ?_⟩
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hcell] <;> omega)))
    rw [cntEq_succ]
    by_cases e : clsKey x.RAB j = t
    · subst e
      rw [if_pos rfl, Function.update_self]
    · rw [if_neg e, Function.update_of_ne (by omega)]
      exact hc t ht

/-- cls[t] += cls[t - 1] for t = 1, …, p. -/
theorem clsPrefix_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsCounted x) σ) :
    Ends lim P d clsPrefix σ (25 * x.p + 8) (ClsState μ x (ClsStarts x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hfirst, hc⟩ := h
  (obtain ⟨⟩ := id pre)
  -- i := 1
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
            -- while i ≤ p; before round j the counter is j + 1, and the cells up to j hold the starts
            
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
  -- while i ≤ p; before round j the counter is j + 1, and the cells up to j hold the starts
  refine Ends.whileConst (fun j σ => ∃ μ'' : ℕ → ℤ,
      σ = ⟨frame (x.locals (j + 1 : ℕ) ad row col pl), μ''⟩ ∧ x.Same μ μ'' ∧
      (∀ t ≤ j, μ'' (x.cls + t) = (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)) ∧
      ∀ t < x.p, j ≤ t → μ'' (x.cls + (t + 1)) = (cntEq (clsKey x.RAB) t (x.n * x.n) : ℕ)) x.p 19
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
    refine ⟨μ', rfl, hrest, fun t ht => ?_, fun t ht _ => hc t ht⟩
    obtain rfl : t = 0 := by omega
    simpa [cntLt] using hfirst
  case done =>
    rintro _ ⟨μ'', rfl, hr, hs, -⟩
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), _, ad, row, col, pl, μ'', rfl, hr, hs⟩
  case round =>
    rintro j _ hj ⟨μ'', rfl, hr, hs, hc⟩
    have hprev := hs j le_rfl
    have hcell := hc j hj le_rfl
    have hle : cntLt (clsKey x.RAB) (j + 1) (x.n * x.n) ≤ x.n * x.n := cntLt_le _ _ _
    have hsum := cntLt_succ_left (clsKey x.RAB) j (x.n * x.n)
    have haddr : ((x.cls : ℤ) + ((j : ℤ) + 1)).toNat = x.cls + (j + 1) := by omega
    have haddr' : ((x.cls : ℤ) + ((j : ℤ) + 1) - 1).toNat = x.cls + j := by omega
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    -- cls[i] := cls[i] + cls[i - 1]
    refine Ends.storeToThen (x.cls + (j + 1)) (cntLt (clsKey x.RAB) (j + 1) (x.n * x.n) : ℕ) ?_
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, haddr', hprev, hcell] <;>
                omega)))
    -- i := i + 1
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (j + 1 + 1 : ℕ) ?_ ?_ ?_);
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
    refine ⟨_, rfl, hr.update ⟨by omega, by omega⟩ _, fun t ht => ?_,
      fun t ht hjt => (Function.update_of_ne (by omega) _ _).trans (hc t ht (by omega))⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ht) with ht | rfl
    · exact (Function.update_of_ne (by omega) _ _).trans (hs t (by omega))
    · exact Function.update_self ..





open Classes in
/-- cur[t] := cls[t] for t < p. -/
theorem clsCopy_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsStarts x) σ) :
    Ends lim P d clsCopy σ (16 * x.p + 6) (ClsState μ x (ClsCopied x)) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hs⟩ := h
  (obtain ⟨⟩ := id pre)
  refine Ends.pass (x := Prime) (y := Cur) (dst := x.cur) (n := x.p)
    (fun t => (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)) (fun j hj => ?_) ?_ hw (by omega) rfl rfl
  · have hcell := (wrote_rest (μ := μ') (dst := x.cur) (j := j)
      (f := fun t => (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)) (a := x.cls + j) (by omega)).trans
      (hs j (by omega))
    simp [Limits.Addr, abs_le, hcell]
    omega
  · rw [update_frame_setLocal]
    exact ⟨_, ad, row, col, pl, _, rfl,
      hrest.trans ((sameOutside_wrote le_rfl).mono (by omega) (by omega)),
      fun t ht => (wrote_rest (by omega)).trans (hs t ht), fun t ht => wrote_done ht⟩










omit hw in
/-- **The pair number i is placed**: its row and its column are written to its place, and the next
free place of its class moves on. -/
theorem ClsPlaced.step (pre : ClassesPre lim μ x) {i : ℕ} (hi : i < x.n * x.n)
    (h : ClsPlaced x i μ') :
    ClsPlaced x (i + 1)
      (Function.update (Function.update (Function.update μ'
        (x.qi + sortPos (clsKey x.RAB) (x.n * x.n) i) (i / x.n : ℕ))
        (x.qj + sortPos (clsKey x.RAB) (x.n * x.n) i) (i % x.n : ℕ))
        (x.cur + clsKey x.RAB i) (sortPos (clsKey x.RAB) (x.n * x.n) i + 1 : ℕ)) := by
  (obtain ⟨⟩ := id pre)
  have hk := pre.key_lt hi
  have hpos := sortPos_lt (clsKey x.RAB) hi
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun j hj => ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact h.keep t ht
  · rw [cntEq_succ]
    by_cases e : clsKey x.RAB i = t
    · subst e
      rw [Function.update_self, if_pos rfl, sortPos, Nat.add_assoc]
    · rw [if_neg e, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact h.next t ht
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have hne : sortPos (clsKey x.RAB) (x.n * x.n) j ≠ sortPos (clsKey x.RAB) (x.n * x.n) i :=
        fun e => absurd (eq_of_sortPos_eq (by omega) hi e) (by omega)
      have hlt := sortPos_lt (clsKey x.RAB) (show j < x.n * x.n by omega)
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.done j hj
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self, Function.update_of_ne (by omega), Function.update_self]
      exact ⟨rfl, rfl⟩

/-- **The pair number i is written to its place.** -/
theorem clsPlaceOne_ends (pre : ClassesPre lim μ x) {i : ℕ} (hi : i < x.n * x.n) (ad pl : ℤ)
    (hrest : x.Same μ μ') (h : ClsPlaced x i μ') :
    Ends lim P d clsPlaceOne ⟨frame (x.locals i ad (i / x.n : ℕ) (i % x.n : ℕ) pl), μ'⟩ 25
      fun σ' => ∃ (ad' pl' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (x.locals i ad' (i / x.n : ℕ) (i % x.n : ℕ) pl'), μ''⟩ ∧
          x.Same μ μ'' ∧ ClsPlaced x (i + 1) μ'' := by
  (obtain ⟨⟩ := id pre)
  have hread := pre.read hrest hi
  have hk := pre.key_lt hi
  have hpos : sortPos (clsKey x.RAB) (x.n * x.n) i < x.n * x.n := sortPos_lt (clsKey x.RAB) hi
  have hcell : μ' (x.cur + clsKey x.RAB i) = (sortPos (clsKey x.RAB) (x.n * x.n) i : ℕ) :=
    h.next _ hk
  have hrow := Nat.div_le_self i x.n
  have hcol := Nat.mod_le i x.n
  have hstep := h.step pre hi
  have hrest' := ((hrest.update (b := x.qi + sortPos (clsKey x.RAB) (x.n * x.n) i)
    ⟨by omega, by omega⟩ (i / x.n : ℕ)).update (b := x.qj + sortPos (clsKey x.RAB) (x.n * x.n) i)
    ⟨by omega, by omega⟩ (i % x.n : ℕ)).update (b := x.cur + clsKey x.RAB i) ⟨by omega, by omega⟩
    (sortPos (clsKey x.RAB) (x.n * x.n) i + 1 : ℕ)
  generalize i / x.n = row at *
  generalize i % x.n = col at *
  -- ad := cur + rab[i]; pl := mem[ad]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (x.cur + clsKey x.RAB i : ℕ) ?_ ?_ ?_);
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
    (refine
        Light.Ends.setToThen (sortPos (clsKey x.RAB) (x.n * x.n) i : ℕ) ?_ ?_ ?_);
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
  -- qi[pl] := row; qj[pl] := col; mem[ad] := pl + 1
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
        Light.Ends.storeToThen (x.qi + sortPos (clsKey x.RAB) (x.n * x.n) i)
          (row : ℕ) ?_ ?_ ?_);
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
        Light.Ends.storeToThen (x.qj + sortPos (clsKey x.RAB) (x.n * x.n) i)
          (col : ℕ) ?_ ?_ ?_);
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
        Light.Ends.storeToThen (x.cur + clsKey x.RAB i)
          (sortPos (clsKey x.RAB) (x.n * x.n) i + 1 : ℕ) ?_ ?_ ?_);
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
  exact ⟨_, _, _, rfl, hrest', hstep⟩

/-- All pairs go to their places. -/
theorem clsPlace_ends (pre : ClassesPre lim μ x) (h : ClsState μ x (ClsCopied x) σ) :
    Ends lim P d clsPlace σ (47 * (x.n * x.n) + 10) (ClsState μ x (ClsPlaced x (x.n * x.n))) := by
  obtain ⟨i, ad, row, col, pl, μ', rfl, hrest, hs, hcur⟩ := h
  (obtain ⟨⟩ := id pre)
  -- row := 0; col := 0
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
            -- for i < nn
            
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
  -- for i < nn
  refine Ends.for (fun j σ => ∃ (ad pl : ℤ) (μ'' : ℕ → ℤ),
      σ = ⟨frame (x.locals j ad (j / x.n : ℕ) (j % x.n : ℕ) pl), μ''⟩ ∧
        x.Same μ μ'' ∧ ClsPlaced x j μ'') (x.n * x.n) 39
    ?start ?round ?done ?bound
  case start =>
    exact ⟨ad, pl, μ', by rw [update_frame_setLocal, Nat.zero_div, Nat.zero_mod]; rfl, hrest, hs,
      fun t ht => by simpa [cntEq] using hcur t ht, fun j hj => absurd hj (by omega)⟩
  case bound =>
    rintro j _ - - ⟨ad, pl, μ'', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨ad, pl, μ'', rfl, hr, hp⟩
    exact ⟨_, ad, _, _, pl, μ'', rfl, hr, hp⟩
  case round =>
    rintro j _ hj - ⟨ad, pl, μ'', rfl, hr, hp⟩
    have hn : 0 < x.n := Nat.pos_of_ne_zero fun e => by simp [e] at hj
    have hnn : x.n ≤ x.n * x.n := Nat.le_mul_of_pos_left x.n hn
    refine Ends.next 25 ((clsPlaceOne_ends hw pre hj ad pl hr hp).mono le_rfl ?_)
    rintro _ ⟨ad', pl', μ₃, rfl, hr', hp'⟩
    refine Ends.nextPair ?_ hn (by omega) (by omega) rfl rfl rfl
    exact ⟨by simp, ad', pl', μ₃, by rw [update_frame_setLocal]; rfl, hr', hp'⟩

end phases

open Classes in
/-- **classes** writes the starts of the classes and the rows and columns of the pairs, class after
class. -/
theorem classes_meets {pClasses : ℕ} (hP : P[pClasses]? = some classesBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (x : ClassesArgs) (μ : ℕ → ℤ) (pre : ClassesPre lim μ x) :
    Meets lim P pClasses d x.vals μ (tClasses x.n x.p) fun _ μ' =>
      SegN μ' x.cls (classStarts x.n x.p x.RAB) ∧ SegN μ' x.qi (queryRows x.n x.p x.RAB) ∧
        SegN μ' x.qj (queryCols x.n x.p x.RAB) ∧ x.Same μ μ' := by
  refine .of_body hP ?_
  (obtain ⟨⟩ := id pre)
  unfold tClasses
  -- pairs := n * n
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
  have h0 : ClsState μ x (fun _ => True) ⟨frame (setLocal x.vals Pairs (x.n * x.n : ℕ)), μ⟩ :=
    ⟨0, 0, 0, 0, 0, μ, by rw [← frame_append_zeros _ 5]; rfl, .refl, trivial⟩
  -- the five phases
  refine Ends.next _ ((clsZero_ends hw pre h0).mono le_rfl fun _ h1 => ?_)
  refine Ends.next _ ((clsCount_ends hw pre h1).mono le_rfl fun _ h2 => ?_)
  refine Ends.next _ ((clsPrefix_ends hw pre h2).mono le_rfl fun _ h3 => ?_)
  refine Ends.next _ ((clsCopy_ends hw pre h3).mono le_rfl fun _ h4 => ?_)
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (clsPlace_ends hw pre h4) ?_ ?_
      | refine Light.Ends.pieceLast (clsPlace_ends hw pre h4) ?_ ?_);
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
    (on_goal -1 => rintro _ ⟨_, _, _, _, _, μ', rfl, hrest, hp⟩)
  have hkeys : ∀ j < x.n * x.n, clsKey x.RAB j < x.p := fun j hj => pre.key_lt hj
  refine ⟨fun t ht => ?_, segN_map_sortedIdx hkeys _ fun j hj => (hp.done j hj).1,
    segN_map_sortedIdx hkeys _ fun j hj => (hp.done j hj).2, hrest⟩
  have hl : t < (classStarts x.n x.p x.RAB).length := by simpa using ht
  have ht' : t < x.p + 1 := by simpa [classStarts] using hl
  rw [List.getElem_map, ← List.getD_eq_getElem _ 0 hl, getD_classStarts x.n x.p x.RAB (by omega)]
  exact hp.keep t (by omega)

end Light.Sec3

end
end

section


/-!
# The table of the chunks

Proof of Theorem 17: "cut it into chunks of at most n²/√D query pairs".  chunks(cls, p, cap, cr, cl,
cw) goes through the `p` classes, whose starts are in the `p + 1` cells from `cls`, cuts each of
them into chunks of at most `cap` places, and writes the residues, the starts and the lengths of the
chunks to `cr`, `cl` and `cw`; the residue of a chunk is the number `rho < p` of its class.  It
returns the number of chunks (`chunks_meets`).  The proof follows the program: one chunk
(`chunksRound_runs`), the chunks of one class (`chunksClass_ends`), all classes.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Chunks

















end Chunks








































































/-! ## The pure side -/

section pure

/-- A class of `hi - lo` places has `⌈(hi - lo)/cap⌉` chunks. -/
theorem length_chunksOf (cap lo hi rho : ℕ) :
    (chunksOf cap lo hi rho).length = (hi - lo) ⌈/⌉ cap := by
  simp [chunksOf]





theorem length_chunkRow (cap : ℕ) (C : List ℕ) (rho : ℕ) :
    (chunkRow cap C rho).length = (C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap :=
  length_chunksOf _ _ _ _





/-- At the start the table is empty. -/
theorem tabAt_zero_zero (cap : ℕ) (C : List ℕ) : tabAt cap C 0 0 = [] := by simp [tabAt]

/-- After all classes the table is complete. -/
theorem tabAt_end (p cap : ℕ) (C : List ℕ) : tabAt cap C p 0 = chunkTabOf p cap C := by
  rw [tabAt, List.take_zero, List.append_nil]
  rfl

/-- After the last chunk of a class the next class begins. -/
theorem tabAt_row (cap : ℕ) (C : List ℕ) (rho : ℕ) :
    tabAt cap C rho ((C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap)
      = tabAt cap C (rho + 1) 0 := by
  rw [tabAt, ← length_chunkRow, List.take_length, tabAt, List.range_succ, List.flatMap_append]
  simp

/-- One more chunk of the class `rho`. -/
theorem tabAt_succ (cap : ℕ) (C : List ℕ) (rho : ℕ) {i : ℕ}
    (hi : i < (C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap) :
    tabAt cap C rho (i + 1) = tabAt cap C rho i ++
      [⟨rho, C.getD rho 0 + i * cap, min cap (C.getD (rho + 1) 0 - C.getD rho 0 - i * cap)⟩] := by
  have hrow : i < (chunkRow cap C rho).length := by rw [length_chunkRow]; exact hi
  rw [tabAt, tabAt, ← List.take_append_getElem hrow, List.append_assoc]
  simp [chunkRow, chunksOf]

/-- As long as a chunk is missing, the table is shorter than the complete one. -/
theorem length_tabAt_lt {p cap : ℕ} (C : List ℕ) {rho i : ℕ} (hrho : rho < p)
    (hi : i < (C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap) :
    (tabAt cap C rho i).length < (chunkTabOf p cap C).length := by
  have hrow := length_chunkRow cap C rho
  have hrows :=
    List.sum_map_range_mono (fun r => (chunkRow cap C r).length) (show rho + 1 ≤ p by omega)
  rw [List.range_succ, List.map_append, List.sum_append] at hrows
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hrows
  have hall : (chunkTabOf p cap C).length
      = ((List.range p).map fun r => (chunkRow cap C r).length).sum := by
    rw [chunkTabOf, List.length_flatMap]
    rfl
  rw [hall, tabAt, List.length_append, List.length_flatMap, List.length_take]
  omega

/-- The time of the rounds, added up: 37 steps for each chunk and 24 for each class. -/
theorem sum_chunks_rounds (cap : ℕ) (C : List ℕ) (q : ℕ) :
    ∑ rho ∈ Finset.range q, (4 + (37 * ((C.getD (rho + 1) 0 - C.getD rho 0) ⌈/⌉ cap) + 20))
      = 37 * (tabAt cap C q 0).length + 24 * q := by
  induction q with
  | zero => simp [tabAt]
  | succ q ih =>
    have hrow : (tabAt cap C (q + 1) 0).length
        = (tabAt cap C q 0).length + (C.getD (q + 1) 0 - C.getD q 0) ⌈/⌉ cap := by
      rw [← tabAt_row cap C q]
      simp [tabAt, length_chunkRow]
    rw [Finset.sum_range_succ, ih, hrow]
    omega

end pure

/-! ## The tables in the memory -/

variable {μ μ' : ℕ → ℤ} {x : ChunksArgs}








/-- One more chunk: each table gets one more entry, and the writes to the other two tables do not
touch it. -/
theorem TabInv.push {T : List Chunk} (h : TabInv μ μ' x T) (pre : ChunksPre lim μ x)
    (hlen : T.length < x.R) (c : Chunk) :
    TabInv μ (Function.update (Function.update (Function.update μ' (x.cr + T.length) c.residue)
      (x.cl + T.length) c.start) (x.cw + T.length) c.len) x (T ++ [c]) := by
  (obtain ⟨⟩ := id pre)
  have hr := h.sr.snoc c.residue
  have hl :=
    SegN.snoc (h.sl.update_out (b := x.cr + T.length) (by simp; omega) (c.residue : ℤ)) c.start
  have hw := SegN.snoc
    ((h.sw.update_out (b := x.cr + T.length) (by simp; omega) (c.residue : ℤ)).update_out
      (b := x.cl + T.length) (by simp; omega) (c.start : ℤ)) c.len
  simp only [List.length_map] at hr hl hw
  refine ⟨?_, ?_, ?_, fun b hb => ?_⟩
  · rw [List.map_append]
    exact (hr.update_out (by simp; omega) _).update_out (by simp; omega) _
  · rw [List.map_append]
    exact hl.update_out (by simp; omega) _
  · rw [List.map_append]
    exact hw
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact h.same b hb

/-- A start of a class, read from a memory in which only the tables have changed. -/
theorem ChunksPre.start (pre : ChunksPre lim μ x) (hsame : x.Same μ μ') {t : ℕ} (ht : t ≤ x.p) :
    μ' (x.cls + t) = ((x.C.getD t 0 : ℕ) : ℤ) ∧ x.C.getD t 0 ≤ x.B := by
  (obtain ⟨⟩ := id pre)
  have hlen : t < x.C.length := by omega
  rw [hsame _ ⟨by omega, by omega, by omega⟩, pre.seg.read hlen]
  exact ⟨rfl, by rw [List.getD_eq_getElem _ 0 hlen]; exact pre.le _ (List.getElem_mem hlen)⟩

/-! ## The program -/

variable (hw : (lim.space : ℤ) ≤ lim.word)

include hw

/-- One chunk. -/
theorem chunksRound_runs {rho pos hi cnt : ℕ} {len : ℤ} (hpos : pos < hi) (hhi : hi < lim.space)
    (hr : x.cr + cnt < lim.space) (hl : x.cl + cnt < lim.space) (hc : x.cw + cnt < lim.space) :
    chunksRound.Runs lim ⟨frame (x.locals rho pos hi cnt len), μ'⟩
      (· = ⟨frame (x.locals rho (pos + min x.cap (hi - pos) : ℕ) hi (cnt + 1 : ℕ)
          (min x.cap (hi - pos) : ℕ)),
        Function.update (Function.update (Function.update μ' (x.cr + cnt) rho) (x.cl + cnt) pos)
          (x.cw + cnt) (min x.cap (hi - pos) : ℕ)⟩) := by
  by_cases hcap : x.cap < hi - pos
  · have htest : (x.cap : ℤ) < (hi : ℤ) - pos := by omega
    rw [show min x.cap (hi - pos) = x.cap by omega]
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, chunksRound,
                        update_frame_setLocal, htest] <;>
                      omega)),
      by simp [chunksRound, update_frame_setLocal, htest]⟩
  · have htest : ¬ (x.cap : ℤ) < (hi : ℤ) - pos := by omega
    rw [show min x.cap (hi - pos) = hi - pos by omega]
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, chunksRound,
                        update_frame_setLocal, htest] <;>
                      omega)),
      by simp [chunksRound, update_frame_setLocal, htest, Nat.cast_sub hpos.le]⟩






/-- The chunks of one class. -/
theorem chunksClass_ends {rho : ℕ} {σ : State} (pre : ChunksPre lim μ x) (hrho : rho < x.p)
    (hσ : ChunksInv μ x rho (tabAt x.cap x.C rho 0) σ) :
    Ends lim P d chunksClass σ (37 * ((x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap) + 16)
      (ChunksInv μ x rho (tabAt x.cap x.C (rho + 1) 0)) := by
  obtain ⟨pos₀, end₀, len₀, μ', rfl, hT⟩ := hσ
  (obtain ⟨⟩ := id pre)
  have hroom : x.table.length ≤ x.R := pre.room
  obtain ⟨hreadLo, hloB⟩ := pre.start hT.same (show rho ≤ x.p by omega)
  obtain ⟨hreadHi, hhiB⟩ := pre.start hT.same (show rho + 1 ≤ x.p by omega)
  have hsucc := fun i hlt => tabAt_succ x.cap x.C rho (i := i) hlt
  have hlenlt : ∀ i, i < (x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap →
      (tabAt x.cap x.C rho i).length < x.table.length := fun i hlt => length_tabAt_lt x.C hrho hlt
  have hiff : ∀ i, i < (x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap ↔
      i * x.cap < x.C.getD (rho + 1) 0 - x.C.getD rho 0 := fun i => Nat.lt_ceilDiv_iff pre.hcap
  rw [← tabAt_row x.cap x.C rho]
  generalize x.C.getD rho 0 = lo at *
  generalize x.C.getD (rho + 1) 0 = hi at *
  generalize (hi - lo) ⌈/⌉ x.cap = rounds at *
  have haddr : ((x.cls : ℤ) + rho + 1).toNat = x.cls + (rho + 1) := by omega
  -- pos := cls[rho]; end := cls[rho + 1]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen lo ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hreadLo]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hreadLo] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hreadLo] <;> omega)));
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
    (refine Light.Ends.setToThen hi ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, haddr,
                hreadHi]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [haddr, hreadHi] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hreadHi] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while pos < end.  Before round i, the first i chunks of the class are in the tables.
  refine Ends.whileBlock (fun i σ => ∃ (len : ℤ) (μ₁ : ℕ → ℤ),
    σ = ⟨frame (x.locals rho (lo + min (i * x.cap) (hi - lo) : ℕ) hi
      (tabAt x.cap x.C rho i).length len), μ₁⟩ ∧
    TabInv μ μ₁ x (tabAt x.cap x.C rho i)) rounds ?start ?round ?done
    (by simp [chunksRound]; omega)
  case start => exact ⟨len₀, μ', by simp, hT⟩
  case round =>
    rintro i _ hround ⟨len, μ₁, rfl, hT₁⟩
    have hlt : i * x.cap < hi - lo := (hiff i).1 hround
    have hlen := hlenlt i hround
    have hpush := hT₁.push pre (by omega) ⟨rho, lo + i * x.cap, min x.cap (hi - lo - i * x.cap)⟩
    rw [← hsucc i hround] at hpush
    rw [show lo + min (i * x.cap) (hi - lo) = lo + i * x.cap by omega]
    refine ⟨by simp, by simp; omega, (chunksRound_runs hw (by omega) (by omega) (by omega)
      (by omega) (by omega)).mono ?_⟩
    rintro _ rfl
    have hleft : hi - (lo + i * x.cap) = hi - lo - i * x.cap := by omega
    have hnext : lo + i * x.cap + min x.cap (hi - lo - i * x.cap) =
        lo + min ((i + 1) * x.cap) (hi - lo) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hlength : (tabAt x.cap x.C rho (i + 1)).length = (tabAt x.cap x.C rho i).length + 1 := by
      rw [hsucc i hround, List.length_append, List.length_singleton]
    exact ⟨(min x.cap (hi - lo - i * x.cap) : ℕ), _, by rw [hleft, hnext, hlength], hpush⟩
  case done =>
    rintro _ ⟨len, μ₁, rfl, hT₁⟩
    have hge : ¬ rounds * x.cap < hi - lo := fun h => absurd ((hiff rounds).2 h) (lt_irrefl _)
    exact ⟨by simp, by simp; omega, _, _, _, _, rfl, hT₁⟩

omit hw in
/-- **chunks** writes the table of the chunks and returns their number. -/
theorem chunks_meets {pChunks : ℕ} (hP : P[pChunks]? = some chunksBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (x : ChunksArgs) (μ : ℕ → ℤ) (pre : ChunksPre lim μ x) :
    Meets lim P pChunks d x.vals μ (tChunks x.p x.table.length) fun r μ' =>
      r = (x.table.length : ℕ) ∧ SegN μ' x.cr (x.table.map (·.residue)) ∧
        SegN μ' x.cl (x.table.map (·.start)) ∧ SegN μ' x.cw (x.table.map (·.len)) ∧
        x.Same μ μ' := by
  refine .of_body hP ?_
  (obtain ⟨⟩ := id pre)
  have hsum := sum_chunks_rounds x.cap x.C x.p
  rw [tabAt_end, ← ChunksArgs.table] at hsum
  unfold tChunks
  -- rho := 0; cnt := 0
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
            -- while rho < p
            
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
  -- while rho < p
  refine Ends.next _ (Ends.while (fun rho σ => ChunksInv μ x rho (tabAt x.cap x.C rho 0) σ) x.p
    (fun rho => 37 * ((x.C.getD (rho + 1) 0 - x.C.getD rho 0) ⌈/⌉ x.cap) + 20) ?start ?round ?done)
    (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)
  case start =>
    refine ⟨0, 0, 0, μ, ?_, by simp [tabAt_zero_zero, SegN], by simp [tabAt_zero_zero, SegN],
      by simp [tabAt_zero_zero, SegN], .refl⟩
    simpa [tabAt_zero_zero] using
      (frame_append_zeros [(x.cls : ℤ), x.p, x.cap, x.cr, x.cl, x.cw, 0, 0, 0, 0] 1).symm
  case round =>
    rintro rho σ hrho hσ
    have hclass := chunksClass_ends (P := P) (d := d) hw pre hrho hσ
    obtain ⟨pos, hi, len, μ', rfl, -⟩ := hσ
    -- the chunks of the class rho; then rho := rho + 1
    refine ⟨by simp, by simp; omega, Ends.next _ (hclass.mono le_rfl ?_) (by omega)⟩
    rintro _ ⟨pos₁, hi₁, len₁, μ₁, rfl, hT⟩
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (rho + 1 : ℕ) ?_ ?_ ?_);
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
    exact ⟨pos₁, hi₁, len₁, μ₁, by simp, hT⟩
  case done =>
    rintro _ ⟨pos, hi, len, μ', rfl, hT⟩
    rw [tabAt_end] at hT
    -- return cnt
    exact ⟨by simp, by simp, Ends.setTo ((tabAt x.cap x.C x.p 0).length : ℕ)
      ⟨by simp [tabAt_end], hT.sr, hT.sl, hT.sw, hT.same⟩ (by simp)
      (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)⟩

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







/-- The chosen prime is at most √D. -/
theorem hostData_p_le (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) :
    (hostData x D g).p ≤ Nat.sqrt D :=
  chosenPrime_le_sqrt x.AB x.BC x.AC hD

/-- The chosen prime is at least 2. -/
theorem two_le_hostData_p (x : TriInst) {D : ℕ} (g : ℕ) (hD : 16 ≤ D) : 2 ≤ (hostData x D g).p :=
  two_le_chosenPrime x.AB x.BC x.AC hD

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





















/-- The need of the solver on an instance with at most cap query pairs is at most supNeed. -/
private theorem need_le_supNeed (need : List ℕ → Need) (n D : ℕ) {cap w : ℕ} (hw : w ≤ cap) :
    (need [n, D, w]).word ≤ (supNeed need n D cap).word ∧
      (need [n, D, w]).cells ≤ (supNeed need n D cap).cells ∧
      (need [n, D, w]).depth ≤ (supNeed need n D cap).depth := by
  have hm : w ∈ Finset.range (cap + 1) := Finset.mem_range.2 (by omega)
  exact ⟨Finset.le_sup (f := fun v => (need [n, D, v]).word) hm,
    Finset.le_sup (f := fun v => (need [n, D, v]).cells) hm,
    Finset.le_sup (f := fun v => (need [n, D, v]).depth) hm⟩

/-- What hostLoop asks of the limits. -/
theorem hostLim_of_ok {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {x : TriInst}
    {fr D g : ℕ} (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    HostLim lim (d + 1) (hostData x D g) x.U (hostAddr x (hostData x D g) fr) need := by
  have hD : 16 ≤ D := hbig.sixteen_le
  have hcells : fr + (chooseCells x.n x.U D + hostLayout x.n x.U D
      + (supNeed need x.n D (queryCapNat x.n D)).cells + 2) ≤ lim.space := hok.cells
  have hdepth : d + (2 * Nat.clog 2 x.n + 8 + (supNeed need x.n D (queryCapNat x.n D)).depth)
      ≤ lim.depth := hok.depth
  have hword : ((hostWord a b x.n x.U D g + (supNeed need x.n D (queryCapNat x.n D)).word : ℕ) : ℤ)
      ≤ lim.word := hok.word
  have hfr := aFr_le (x := x) (g := g) hD fr
  have hp := hostData_p_le x g hD
  have hm := hostData_m_le hbig
  have hlay : 2 * Nat.sqrt D ≤ hostLayout x.n x.U D := by unfold hostLayout; omega
  exact
    { space := hok.space
      fr := by change aFr (hostData x D g) x.U fr < lim.space; omega
      prime := by omega
      count := le_word_of_le_hostWord hok (hm.trans (by unfold hostWord; omega))
      step := le_word_of_le_hostWord hok (by
        change x.n + pieceSizeNat D g ≤ _
        unfold hostWord
        omega)
      weights := le_word_of_le_hostWord hok
      depth := by omega
      solver := fun t ht => by
        have hwc : (hostData x D g).w t ≤ queryCapNat x.n D := (hostData x D g).w_le_cap ht
        obtain ⟨hsword, hscells, hsdepth⟩ := need_le_supNeed need x.n D hwc
        change (need [x.n, D, (hostData x D g).w t]).Ok lim (aFr (hostData x D g) x.U fr)
          (d + 1 + 1)
        exact ⟨le_trans (Nat.cast_le.2 (hsword.trans (Nat.le_add_left _ _))) hword, by omega,
          hok.space, by omega⟩ }

end Light.Sec3

end
end

section


/-!
# Pure facts about the starts of the classes and the table of chunks

Proof of Theorem 17.  The `n²` pairs `(a, b)` are listed class after class, where the class
of a residue `ϱ < p` holds the pairs whose weight is congruent to `ϱ` modulo the prime `p`, and each
class is cut into chunks of at most `cap` pairs.  The list of the starts of the classes has `p + 1`
entries, none above `n²`; the table of chunks has at most `n² + p` entries.
-/

public section

namespace ThreeSumApsp.Spec

/-- The list of the starts of the classes has one entry for each residue, and one more for the
end. -/
theorem length_classStarts (n p : ℕ) (RAB : List ℕ) : (classStarts n p RAB).length = p + 1 := by
  simp [classStarts]

/-- A class starts at a place of the list of all n² pairs, or at its end. -/
theorem classStart_le_sq (n : ℕ) (RAB : List ℕ) (rho : ℕ) : classStart n RAB rho ≤ n * n := by
  rw [classStart_eq_length_filter]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-- No entry of the list of the starts of the classes is above n². -/
theorem le_of_mem_classStarts {n p : ℕ} {RAB : List ℕ} {x : ℕ} (hx : x ∈ classStarts n p RAB) :
    x ≤ n * n := by
  obtain ⟨rho, -, rfl⟩ := List.mem_map.1 hx
  exact classStart_le_sq n RAB rho

/-- If `cap ≥ 1` and every residue is below `p`, the table of chunks has at most `n² + p` entries.
This is the number of cells that the host procedure of Theorem 17 reserves for each of its three
components. -/
theorem length_chunkTab_le_add {n p cap : ℕ} {RAB : List ℕ} (hcap : 1 ≤ cap)
    (hlt : ∀ i < n * n, RAB.getD i 0 < p) : (chunkTab n p cap RAB).length ≤ n * n + p := by
  have hlen := length_chunkTab_le hcap hlt
  have hdiv := Nat.div_le_self (n * n) cap
  omega

end ThreeSumApsp.Spec

end
end

section


/-!
# The host of Theorem 17: the arrays and the loop

The third part of the host procedure `et17` (Exact Triangle by Theorem 17) fills the table of
doubles and the three lists of residues (`resid_then`), sorts the pairs into classes and cuts the
classes into chunks (`classes_then`), and calls the loop over the instances.

`et17Tables_spec` is the specification of the whole part: within `hostRunTime` steps, local 0 holds
the bit `found m` of the loop over the instances, and the cells below the free pointer are
unchanged.  Three lemmas connect the calls to the loop: `ready_of` (a run of et17 provides what this
part needs), `hostMem_of` (the arrays that the loop reads are in the memory) and `hostLay_of` (they
lie where the loop expects them).
-/

@[expose] public section

open ThreeSumApsp.Spec

namespace Light.Sec3

open ThreeSumApsp

namespace Et17

/-- A call that puts its result into the local Small. -/
theorem setLocal_res (x : TriInst) (X : HostData) (fr : ℕ) (g s nch res r : ℤ) :
    setLocal (locals x X fr g s nch res) Small r = locals x X fr g s nch r := rfl























variable {lim : Limits} {P : Program} {d : ℕ} {x : TriInst} {X : HostData} {μ : ℕ → ℤ} {fr : ℕ}

/-- The places of the lists of residues: they stand one after the other behind the table of doubles,
and end where the array of the classes begins, below the free pointer of the solver. -/
private theorem resid_places (X : HostData) (U fr : ℕ) :
    aRab X U fr = fr + (bitLen U + 1) ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCls X U fr ≤ aFr X U fr := by
  have := host_places X U fr
  omega

/-- The places of the arrays of the classes and the chunks: they stand one after the other behind
the lists of residues, and end at aX, the first matrix of the instance that is handed to the solver,
below the free pointer of the solver. -/
private theorem class_places (X : HostData) (U fr : ℕ) :
    aRbc X U fr = aRab X U fr + X.n * X.n ∧ aRac X U fr = aRbc X U fr + X.n * X.n ∧
      aCls X U fr = aRac X U fr + X.n * X.n ∧ aCur X U fr = aCls X U fr + (X.p + 1) ∧
      aQi X U fr = aCur X U fr + X.p ∧ aQj X U fr = aQi X U fr + X.n * X.n ∧
      aCr X U fr = aQj X U fr + X.n * X.n ∧ aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧
      aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧ aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧
      aX X U fr ≤ aFr X U fr := by
  have := host_places X U fr
  omega




















/-- What residues needs, for a matrix below the free pointer and a destination between the table of
doubles and the end of the arrays. -/
theorem Ready.residuesPre (h : Ready lim d x X μ fr) {μ' : ℕ → ℤ} {src dst : ℕ} {l : List ℤ}
    (hdbl : Seg μ' fr (dblList X.p (bitLen x.U))) (hsrc : Seg μ' src l)
    (hlen : l.length = X.n * X.n) (hle : AbsLe l x.U) (hbelow : src + X.n * X.n ≤ fr)
    (hlow : fr + (bitLen x.U + 1) ≤ dst := by omega)
    (hhigh : dst + X.n * X.n < lim.space := by omega) :
    ResiduesPre lim μ' src dst (X.n * X.n) fr X.p (bitLen x.U) x.U l :=
  { hw := h.space
    prime := h.prime
    segDbl := hdbl
    segSrc := hsrc
    length := hlen
    le := hle
    lt := Nat.lt_size_self _
    spaceDbl := by omega
    spaceSrc := by omega
    spaceDst := by omega
    count := by omega
    apartSrc := by omega
    apartDbl := by omega
    word := h.word }

/-- **The table of doubles and the three lists of residues**, followed by the rest t of the text. -/
theorem resid_then {pDbl pResid pResidues : ℕ} (hDbl : P[pDbl]? = some dblTableBody)
    (hResid : P[pResid]? = some residBody) (hResidues : P[pResidues]? = some (residuesBody pResid))
    (hr : Ready lim d x X μ fr) {g s : ℤ} {t : Stmt} {T : ℕ} {Q : State → Prop}
    (h : ∀ res μ', ResidMem x X fr μ μ' → Ends lim P d t ⟨frame (locals x X fr g s 0 res), μ'⟩
      (T - (tDblTable (bitLen x.U) + 3 * tResidues (X.n * X.n) (bitLen x.U) + 26)) Q)
    (hT : tDblTable (bitLen x.U) + 3 * tResidues (X.n * X.n) (bitLen x.U) + 26 ≤ T) :
    Ends lim P d
      ((Light.Stmt.seq (.call pDbl [v Free, v ThePrime, v Bits] Small)
         (Light.Stmt.seq
           (.call pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small)
           (Light.Stmt.seq
             (.call pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small)
             (Light.Stmt.seq
               (.call pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small)
               t)))))
      ⟨frame (locals x X fr g s 0 0), μ⟩ T Q := by
  have hdepth := hr.depth
  have htop := hr.top
  have hplaces := resid_places X x.U fr
  have lenAB := hr.lenAB
  have lenBC := hr.lenBC
  have lenAC := hr.lenAC
  have hAB := hr.belowAB
  have hBC := hr.belowBC
  have hAC := hr.belowAC
  have hword : ((X.p * 2 ^ bitLen x.U : ℕ) : ℤ) ≤ lim.word := le_trans (by
    exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)))
    hr.word
  have lenDbl : (dblList X.p (bitLen x.U)).length = bitLen x.U + 1 := by simp [dblList]
  have lenRAB : X.RAB.length = X.n * X.n := (length_residList _ _).trans hr.lenAB
  have lenRBC : X.RBC.length = X.n * X.n := (length_residList _ _).trans hr.lenBC
  -- Small := pDbl(Free, ThePrime, Bits)
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
            ((dblTable_meets (dst := fr) (p := X.p) (len := bitLen x.U) hDbl
                hr.space (by omega) hword)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (dblTable_meets (dst := fr) (p := X.p) (len := bitLen x.U) hDbl
              hr.space (by omega) hword)
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
        ((rintro r₁ μ₁ ⟨hdbl, same₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [setLocal_res]
  -- Small := pResidues(AdrAB, ResAB, SizeSq, Free, Bits)
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
            ((residues_meets hResidues hResid (by omega)
                (hr.residuesPre (dst := aRab X x.U fr) hdbl hr.segAB.keep hr.lenAB
                  hr.leAB hr.belowAB))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (residues_meets hResidues hResid (by omega)
              (hr.residuesPre (dst := aRab X x.U fr) hdbl hr.segAB.keep hr.lenAB
                hr.leAB hr.belowAB))
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
        ((rintro r₂ μ₂ ⟨hrab, same₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [setLocal_res]
  -- Small := pResidues(AdrBC, ResBC, SizeSq, Free, Bits)
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
            ((residues_meets hResidues hResid (by omega)
                (hr.residuesPre (dst := aRbc X x.U fr) hdbl.keep hr.segBC.keep
                  hr.lenBC hr.leBC hr.belowBC))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (residues_meets hResidues hResid (by omega)
              (hr.residuesPre (dst := aRbc X x.U fr) hdbl.keep hr.segBC.keep
                hr.lenBC hr.leBC hr.belowBC))
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
        ((rintro r₃ μ₃ ⟨hrbc, same₃⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [setLocal_res]
  -- Small := pResidues(AdrAC, ResAC, SizeSq, Free, Bits)
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
            ((residues_meets hResidues hResid (by omega)
                (hr.residuesPre (dst := aRac X x.U fr) hdbl.keep hr.segAC.keep
                  hr.lenAC hr.leAC hr.belowAC))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (residues_meets hResidues hResid (by omega)
              (hr.residuesPre (dst := aRac X x.U fr) hdbl.keep hr.segAC.keep
                hr.lenAC hr.leAC hr.belowAC))
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
        ((rintro r₄ μ₄ ⟨hrac, same₄⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [setLocal_res]
  exact (h r₄ μ₄ ⟨hrab.keep, hrbc.keep, hrac, by ((try refine Light.SameOn.cell ?_);
                                                          (intro apspMacro_262731_0 apspMacro_262731_1);
                                                          (first
                                                            |
                                                              ((((repeat
                                                                        (((with_reducible
                                                                                rename Light.SameOn _ _ _ => apspMacro_262731_2));
                                                                          ((try
                                                                                have :=
                                                                                  apspMacro_262731_2 apspMacro_262731_0 (by omega)));
                                                                          (revert apspMacro_262731_2)));
                                                                    (intros);
                                                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                (omega))
                                                            |
                                                              ((simp [] at apspMacro_262731_1);
                                                                (((repeat
                                                                        (((with_reducible
                                                                                rename Light.SameOn _ _ _ => apspMacro_262731_3));
                                                                          ((try
                                                                                have :=
                                                                                  apspMacro_262731_3 apspMacro_262731_0 (by omega)));
                                                                          (revert apspMacro_262731_3)));
                                                                    (intros);
                                                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                (omega))
                                                            |
                                                              ((((repeat
                                                                        (((with_reducible
                                                                                rename Light.SameOn _ _ _ => apspMacro_262731_4));
                                                                          ((try
                                                                                have :=
                                                                                  apspMacro_262731_4 apspMacro_262731_0 (by omega)));
                                                                          (revert apspMacro_262731_4)));
                                                                    (intros);
                                                                    (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                (fail
                                                                    "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                              SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                              its condition K x does not follow from the hypotheses."))))⟩).mono (by simp; omega) fun _ hQ => hQ

/-- There are at most n² + p chunks. -/
theorem Ready.chunkCount_le (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap) :
    X.chunkCount ≤ X.n * X.n + X.p :=
  length_chunkTab_le_add hcap fun i hi => lt_of_mem_residList hr.prime (by
    rw [List.getD_eq_getElem _ _ (by rw [HostData.RAB, length_residList, hr.lenAB]; exact hi)]
    exact List.getElem_mem _)

/-- **The classes and the chunks**, followed by the rest t of the text. -/
theorem classes_then {pClasses pChunks : ℕ} (hClasses : P[pClasses]? = some classesBody)
    (hChunks : P[pChunks]? = some chunksBody) (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap)
    {μ₁ : ℕ → ℤ} (hrab : SegN μ₁ (aRab X x.U fr) X.RAB) {g s res : ℤ} {t : Stmt} {T : ℕ}
    {Q : State → Prop}
    (h : ∀ res' μ', ClassMem x X fr μ₁ μ' → Ends lim P d t
      ⟨frame (locals x X fr g s X.chunkCount res'), μ'⟩
      (T - (tClasses X.n X.p + tChunks X.p X.chunkCount + 17)) Q)
    (hT : tClasses X.n X.p + tChunks X.p X.chunkCount + 17 ≤ T) :
    Ends lim P d
      ((Light.Stmt.seq
         (.call pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols]
           Small)
         (Light.Stmt.seq
           (.call pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks)
           t)))
      ⟨frame (locals x X fr g s 0 res), μ₁⟩ T Q := by
  have hchunks : X.chunkCount = (chunkTabOf X.p X.cap (classStarts X.n X.p X.RAB)).length := rfl
  rw [hchunks] at h hT
  have hdepth := hr.depth
  have hp := hr.prime
  have htop := hr.top
  have hplaces := class_places X x.U fr
  have lenRAB : X.RAB.length = X.n * X.n := (length_residList _ _).trans hr.lenAB
  have ltRAB : ∀ r ∈ X.RAB, r < X.p := fun r hmem => lt_of_mem_residList (by omega) hmem
  have hroom : (chunkTabOf X.p X.cap (classStarts X.n X.p X.RAB)).length ≤ X.n * X.n + X.p :=
    hr.chunkCount_le hcap
  -- Small := pClasses(ResAB, Size, ThePrime, Cls, Cur, Rows, Cols)
  refine Ends.callToThen (classes_meets hClasses hr.space
    { rab := aRab X x.U fr, n := X.n, p := X.p, cls := aCls X x.U fr, cur := aCur X x.U fr,
      qi := aQi X x.U fr, qj := aQj X x.U fr, RAB := X.RAB } μ₁
    { seg := hrab, len := lenRAB, lt := ltRAB }) ?_ (by simp)
  rintro r₁ μ₂ ⟨hcls, hqi, hqj, same₂⟩
  dsimp only at hcls hqi hqj same₂
  rw [setLocal_res]
  -- NumChunks := pChunks(Cls, ThePrime, Cap, TabR, TabL, TabW)
  refine Ends.callToThen (chunks_meets hChunks hr.space
    { cls := aCls X x.U fr, p := X.p, cap := X.cap, cr := aCr X x.U fr, cl := aCl X x.U fr,
      cw := aCw X x.U fr, R := X.n * X.n + X.p, B := X.n * X.n, C := classStarts X.n X.p X.RAB } μ₂
    { seg := hcls, len := length_classStarts X.n X.p X.RAB,
      le := fun y hy => le_of_mem_classStarts hy, room := hroom }) ?_ (by simp)
    (hT := by simp only [ChunksArgs.table]; first
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
  rintro _ μ₃ ⟨rfl, hcr, hcl, hcw, same₃⟩
  simp only [ChunksArgs.table, ChunksArgs.Same] at hcr hcl hcw same₃ ⊢
  have hsorted : (sortedIdx X.n X.p X.RAB).length ≤ X.n * X.n := by
    rw [length_sortedIdx_eq]
    exact classStart_le_sq X.n X.RAB X.p
  have keep : ∀ {a : ℕ} {l : List ℕ}, SegN μ₂ a l → a + l.length ≤ aCr X x.U fr → SegN μ₃ a l := by
    intro a l hs hle
    refine Seg.congr hs fun i hi => same₃ _ ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩ <;>
      (simp only [List.length_map] at hi; omega)
  refine (h r₁ μ₃ ⟨keep hqi (by simp only [HostData.QI, queryRows, List.length_map]; omega),
    keep hqj (by simp only [HostData.QJ, queryCols, List.length_map]; omega), hcr, hcl, hcw,
    fun c hc => ?_⟩).mono (by simp; omega) fun _ hQ => hQ
  exact (same₃ c ⟨by omega, by omega, by omega⟩).trans (same₂ c (by simp only [Outside]; omega))

/-- Where the arrays lie, for the addresses of et17. -/
theorem hostLay_of (hr : Ready lim d x X μ fr) (hchunks : X.chunkCount ≤ X.n * X.n + X.p) :
    HostLay X (hostAddr x X fr) := by
  (obtain ⟨⟩ := id hr)
  have hplaces := host_places X x.U fr
  have hcomm : X.D * X.n = X.n * X.D := Nat.mul_comm _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun t ht => ?_⟩
  case refine_13 =>
    have := X.w_le_cap ht
    simp only [hostAddr]
    omega
  all_goals
    simp only [hostAddr]
    omega

/-- The arrays that the loop over the instances reads are in the memory. -/
theorem hostMem_of (hr : Ready lim d x X μ fr) {μ₁ μ₂ : ℕ → ℤ}
    (hresid : ResidMem x X fr μ μ₁) (hclass : ClassMem x X fr μ₁ μ₂) :
    HostMem X (hostAddr x X fr) μ₂ := by
  ((obtain ⟨⟩ := id hr); (obtain ⟨⟩ := id hresid); (obtain ⟨⟩ := id hclass))
  have hplaces := resid_places X x.U fr
  have lenRAC : X.RAC.length = X.n * X.n := (length_residList _ _).trans hr.lenAC
  have lenRBC : X.RBC.length = X.n * X.n := (length_residList _ _).trans hr.lenBC
  exact
    { segAB := hr.segAB.keep
      segBC := hr.segBC.keep
      segAC := hr.segAC.keep
      segRAC := hresid.rac.keep
      segRBC := hresid.rbc.keep
      segQI := hclass.qi
      segQJ := hclass.qj
      segCR := hclass.cr
      segCL := hclass.cl
      segCW := hclass.cw }

/-- What the third part needs holds for the data of a run of et17. -/
theorem ready_of {need : List ℕ → Need} {D g a b : ℕ} (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ready lim d x (hostData x D g) μ fr := by
  have hD16 := hbig.sixteen_le
  have hcells := hok.cells
  have hdepth := hok.depth
  have htop := aFr_le (x := x) (g := g) hD16 fr
  have hp := two_le_hostData_p x g hD16
  have hps := Nat.mul_le_mul_right (2 ^ (bitLen x.U + 1)) (hostData_p_le x g hD16)
  simp only [hostNeedAt] at hcells hdepth
  exact
    { space := hok.space
      depth := by omega
      prime := by omega
      word := le_word_of_le_hostWord hok
      top := by omega
      segAB := hpre.segAB
      segBC := hpre.segBC
      segAC := hpre.segAC
      lenAB := hpre.lenAB
      lenBC := hpre.lenBC
      lenAC := hpre.lenAC
      leAB := hpre.leAB
      leBC := hpre.leBC
      leAC := hpre.leAC
      belowAB := hpre.belowAB
      belowBC := hpre.belowBC
      belowAC := hpre.belowAC }

end Et17

open Et17 in
/-- **The third part of et17**: the result of the loop over the instances; only cells from the free
pointer on change. -/
theorem et17Tables_spec_sourceProof {P₀ R : Program} {ν : Et17Nums} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    {Dfun Gfun tD tG wD wG : ℕ → ℕ} (C : Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG)
    {lim : Limits} {d : ℕ} (x : TriInst) (μ : ℕ → ℤ) (fr D g a b : ℕ) (hpre : x.Pre μ fr)
    (hbig : BigCase x.n D g) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (et17Tables ν) ⟨frame (et17LocB x fr D g), μ⟩
      (hostRunTime Tn (hostData x D g) x.U)
      fun σ' => σ'.loc 0 = bit ((hostData x D g).found (hostData x D g).m) ∧ Kept μ σ'.mem fr := by
  have hr := ready_of hpre hbig hok
  have hlim := hostLim_of_ok hbig hok
  have hv := hostData_valid hpre hbig
  unfold et17LocB
  generalize hostData x D g = X at hr hlim hv ⊢
  have hdepth := hr.depth
  have hfr : fr ≤ aX X x.U fr := by
    have := host_places X x.U fr
    omega
  unfold et17Tables hostRunTime
  -- the table of doubles and the residues; the classes and the chunks
  refine resid_then C.hDbl C.hResid C.hResidues hr (fun r₁ μ₁ hresid => ?_) (by omega)
  refine classes_then C.hClasses C.hChunks hr hv.cap_pos hresid.rab
    (fun r₂ μ₂ hclass => ?_) (by omega)
  -- NumInst := NumPieces * NumChunks
  have hcount := hlim.count
  have hm : (X.m : ℤ) = (X.h : ℤ) * X.chunkCount := by
    rw [HostData.m]
    push_cast
    rfl
  have hpos : (0 : ℤ) ≤ (X.h : ℤ) * X.chunkCount := by positivity
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (X.m : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hm]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hm] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hm] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- the result is pLoop(…)
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
            ((Meets.of_body (Q := fun r μ' =>
                r = bit (X.found X.m) ∧ Kept μ₂ μ' (hostAddr x X fr).x) C.hLoop
                (hostLoop_spec C.loop ⟨hv, hr.leAB, hr.leBC, hr.leAC⟩
                  (hostMem_of hr hresid hclass)
                  (hostLay_of hr (hr.chunkCount_le hv.cap_pos)) hlim))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (Meets.of_body (Q := fun r μ' =>
              r = bit (X.found X.m) ∧ Kept μ₂ μ' (hostAddr x X fr).x) C.hLoop
              (hostLoop_spec C.loop ⟨hv, hr.leAB, hr.leBC, hr.leAC⟩
                (hostMem_of hr hresid hclass)
                (hostLay_of hr (hr.chunkCount_le hv.cap_pos)) hlim))
            ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hostLoopArgs, hostAddr]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hostLoopArgs, hostAddr] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hostLoopArgs, hostAddr] <;>
              omega)));
    (on_goal -1 =>
        ((rintro r μ₃ ⟨rfl, hkept⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  refine ⟨rfl, fun c hc => ?_⟩
  have hcls : fr ≤ aCls X x.U fr := by
    have := host_places X x.U fr
    omega
  exact (hkept c (lt_of_lt_of_le hc hfr)).trans ((hclass.same c (Or.inl (by omega))).trans
    (hresid.same c (Or.inl hc)))

end Light.Sec3

end
end


theorem solution : ∀ {P₀ R : Light.Program} {ν : Light.Sec3.Et17Nums} {Tn : List.{0} Nat → Nat} {need : List.{0} Nat → Light.Need}
  {Dfun Gfun tD tG wD wG : Nat → Nat},
  Light.Sec3.Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG →
    ∀ {lim : Light.Limits} {d : Nat} (x : Light.TriInst) (μ : Nat → Int) (fr D g a b : Nat),
      x.Pre μ fr →
        Light.Sec3.BigCase x.n D g →
          (Light.Sec3.hostNeedAt a b need x.n x.U D g).Ok lim fr d →
            Light.Ends lim
              (@HAppend.hAppend.{0, 0, 0} Light.Program Light.Program Light.Program
                (@instHAppendOfAppend.{0} Light.Program (@List.instAppend.{0} Light.Stmt)) P₀ R)
              d (Light.Sec3.et17Tables ν) { loc := Light.frame (Light.Sec3.et17LocB x fr D g), mem := μ }
              (Light.Sec3.hostRunTime Tn (Light.Sec3.hostData x D g) x.U) fun (σ' : Light.State) =>
              And
                (@Eq.{1} Int (σ'.loc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (Light.Sec3.bit ((Light.Sec3.hostData x D g).found (Light.Sec3.hostData x D g).m)))
                (Light.Kept μ σ'.mem fr) := by
  exact @Light.Sec3.et17Tables_spec_sourceProof

#print axioms solution
