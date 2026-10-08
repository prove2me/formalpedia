-- Prove2me | solution 1 for Light.Sec3.claim_VW13_Theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:28:45.631983+00:00
-- url     : https://prove2.me/submissions/50fa1d73-87b5-4f69-a803-64a6ee35c365

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
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem21b_NegativeTriangle
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_NegativeTriangle
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_BinaryPrefixes
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
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
import Theorems.Thm_ThreeSumApsp_Theorem21_hasNegativeTriangle_iff
import Theorems.Thm_ThreeSumApsp_pref_step

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







/-- An address fits in a word if the memory is not larger than the largest word. -/
theorem Limits.Addr.abs_le {a : ℤ} (h : lim.Addr a) (hw : (lim.space : ℤ) ≤ lim.word) :
    |a| ≤ lim.word := by
  rw [abs_of_nonneg h.1]; exact h.2.le.trans hw

/-- A natural number below the size of the memory is an address, and fits in a word. -/
theorem Limits.addr_of_lt (hw : (lim.space : ℤ) ≤ lim.word) {x : ℕ} (hx : x < lim.space) :
    lim.Addr (x : ℤ) ∧ |(x : ℤ)| ≤ lim.word := by
  have h : lim.Addr (x : ℤ) := ⟨Int.natCast_nonneg x, by exact_mod_cast hx⟩
  exact ⟨h, h.abs_le hw⟩







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




























/-- **Counting loops whose body may change scratch variables.**  S j s μ' is the state before round
j, with the values s of the scratch variables and the memory μ'; I j holds of the memory.  The
counter of S j s μ' holds j, and S (j + 1) s μ' is S j s μ' with the counter increased; for a shape
fun j s μ' => ⟨frame [.., j, s], μ'⟩ both are proved by default.  The bound hi gives n, n fits in a
word, and the body keeps the shape and takes at most b steps. -/
theorem Ends.forShape {β : Type} {loc : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt}
    (S : ℕ → β → (ℕ → ℤ) → State) (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (s₀ : β) (start : I 0 μ)
    (round : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body (S j s μ') b fun σ' => ∃ s' μ'', σ' = S j s' μ'' ∧ I (j + 1) μ'')
    (done : ∀ (s : β) (μ' : ℕ → ℤ), I n μ' → Q (S n s μ'))
    (first : (⟨Function.update loc i 0, μ⟩ : State) = S 0 s₀ μ := by
      first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (bound : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j ≤ n → I j μ' → hi.Gives lim (S j s μ') n := by
      intros; (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (counter : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), (S j s μ').loc i = j := by intros; simp)
    (next : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ),
      (⟨Function.update (S j s μ').loc i ((j : ℤ) + 1), (S j s μ').mem⟩ : State) =
        S (j + 1) s μ' := by
      intros; first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
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
  refine Ends.for (fun j σ' => ∃ s μ', σ' = S j s μ' ∧ I j μ') n b ⟨s₀, μ, first, start⟩ ?_ ?_ ?_
    hn hT
  · rintro j _ hj - ⟨s, μ', rfl, hI⟩
    refine (round j s μ' hj hI).mono le_rfl ?_
    rintro _ ⟨s', μ'', rfl, hI'⟩
    exact ⟨counter j s' μ'', s', μ'', next j s' μ'', hI'⟩
  · rintro _ - ⟨s, μ', rfl, hI⟩
    exact done s μ' hI
  · rintro j _ hj - ⟨s, μ', rfl, hI⟩
    exact bound j s μ' hj hI

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

/-- A write outside the cells that have been written can be done first. -/
theorem update_wrote {y : ℕ} (hy : Outside dst j y) (w : ℤ) :
    Function.update (wrote μ dst f j) y w = wrote (Function.update μ y w) dst f j := by
  funext a
  by_cases ha : a = y
  · subst ha
    rw [Function.update_self, wrote_rest hy, Function.update_self]
  · simp only [wrote, Function.update_of_ne ha]

/-- Writing `j ≤ n` cells from `dst` changes no cell outside the `n` cells from `dst`. -/
theorem sameOutside_wrote {n : ℕ} (h : j ≤ n) : SameOutside μ (wrote μ dst f j) dst n :=
  fun _ hb => wrote_rest (by omega)

/-! ## The tactics -/









































end Light

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





















/-- Entry `i < l.length` of `l.map f`, whatever the two defaults. Mathlib's `List.getD_map` is for
all `i`, with the default `f d`. -/
theorem getD_map_of_lt (f : α → β) {l : List α} {i : ℕ} (hi : i < l.length) (d : α) (d' : β) :
    (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getD_eq_getElem _ _ hi,
    List.getElem_map]




























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









/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_43548_0 apspMacro_43548_1);
                                                                                  (first
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_43548_2));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_43548_2 apspMacro_43548_0 (by omega)));
                                                                                                  (revert apspMacro_43548_2)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((simp [] at apspMacro_43548_1);
                                                                                        (((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_43548_3));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_43548_3 apspMacro_43548_0 (by omega)));
                                                                                                  (revert apspMacro_43548_3)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_43548_4));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_43548_4 apspMacro_43548_0 (by omega)));
                                                                                                  (revert apspMacro_43548_4)));
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
# Logarithms and real powers

Small facts on `Real.log`, `Real.logb`, `Nat.clog`, `Real.sqrt` and real powers that the estimates
of the paper use silently.

* Values, in the namespace `Real` and named by Mathlib's convention: `1 / 2 < log 2 < 1`,
  `log 4 = 2 log 2`, `log 9 = 2 log 3`, `1 ≤ log 4`, `1 / 2 ≤ log x` for `x ≥ 2`, `1 ≤ log x` for
  `x ≥ 3`, `log₂ 7 < 2.81`, `4 ≤ √D` for `D ≥ 16`.
* The rounded logarithm: `⌈log_b n⌉ < log_b n + 1` (`Real.natCast_clog_lt_logb_add_one`),
  `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)` (`Real.pow_clog_le_mul_rpow_logb`).
* The definition `logU u = log (max u 2)`, the paper's `log U`.
-/

@[expose] public section

namespace Real

/-! ### Values -/

/-- `1 / 2 < log 2`. -/
theorem one_half_lt_log_two : 1 / 2 < log 2 :=
  lt_trans (by norm_num) log_two_gt_d9










































/-! ### The rounded logarithm `Nat.clog` -/




















end Real

namespace ThreeSumApsp






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
# The problems for Section 3.4, read from lists of integers

A routine has its input in arrays.  Here an array is a list of integers, a matrix is stored row by
row, and a cell is read with `List.getD _ _ 0` (`entry`).  This file says which instance of Exact
Triangle, Negative Triangle, Convolution-3SUM, 3SUM or APSP such lists hold (`vecOf`, `triOf`,
`graphOf`), and what the (min,+)-product of two lists is (`minPlusEntry`, `minPlusList`).  Two
operations on matrices serve several reductions: `affL m c` replaces each entry `x` by `m x + c`,
and `subMat` cuts out a block.

An entry of the (min,+)-product is computed as a running minimum.  It is at most each of the sums
`A[i,k] + B[k,j]` (`minPlusEntry_le`) and it is one of them (`exists_minPlusEntry_eq`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Instances -/

























/-- The weights of the instance read from three lists are bounded if the numbers of the lists
are. -/
theorem triOf_bounded {n U : ℕ} {AB BC AC : List ℤ} (hAB : AbsLe AB U) (hBC : AbsLe BC U)
    (hAC : AbsLe AC U) : (triOf n AB BC AC).WeightsBoundedBy (U : ℤ) :=
  ⟨fun _ _ => AbsLe.abs_getD_le (Int.natCast_nonneg U) hAB _,
    fun _ _ => AbsLe.abs_getD_le (Int.natCast_nonneg U) hBC _,
    fun _ _ => AbsLe.abs_getD_le (Int.natCast_nonneg U) hAC _⟩

/-! ## Operations on matrices -/




/-- The list of the numbers `m x + c` is as long as the list of the `x`. -/
@[simp] theorem length_affL (m c : ℤ) (l : List ℤ) : (affL m c l).length = l.length := by
  simp [affL]






















/-! ## The (min,+)-product -/












































end ThreeSumApsp.Spec

end
end

section


/-!
# The prefixes of a binary representation, one bit at a time

The prefixes `⌊z/2^ℓ⌋` of a number `0 ≤ z < 2^L` are computed without division, from the level
`ℓ = L` down to `ℓ = 0`.  Next to the prefix `q = ⌊z/2^ℓ⌋` (`prefQ`) one keeps the rest of the
number, moved to the top: `r = (z mod 2^ℓ) 2^(L-ℓ) < 2^L` (`prefR`).  One step doubles `r`; if the
result reaches `2^L`, then the next bit of `z` is 1 (`pref_step`).  The bit is the binary digit
number `ℓ` of `z` (`testBit_iff_shift`).  One step on lists of numbers is `zipWith_shiftQ` and
`map_shiftR`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Prefixes, one bit at a time -/













/-- At the top level the prefix is 0. -/
theorem prefQ_start {L : ℕ} {z : ℤ} (h0 : 0 ≤ z) (h : z < 2 ^ L) : prefQ L z = 0 :=
  Int.ediv_eq_zero_of_lt h0 h

/-- At the top level the rest is the number itself. -/
theorem prefR_start {L : ℕ} {z : ℤ} (h0 : 0 ≤ z) (h : z < 2 ^ L) : prefR L L z = z := by
  simp [prefR, Int.emod_eq_of_lt h0 h]



































/-- The prefixes of a nonnegative number are nonnegative. -/
theorem prefQ_nonneg {z : ℤ} (h0 : 0 ≤ z) (ℓ : ℕ) : 0 ≤ prefQ ℓ z :=
  Int.ediv_nonneg h0 (by positivity)

/-- The prefixes of a nonnegative number are at most the number. -/
theorem prefQ_le {z : ℤ} (h0 : 0 ≤ z) (ℓ : ℕ) : prefQ ℓ z ≤ z := Int.ediv_le_self _ h0

/-- The rests are nonnegative. -/
theorem prefR_nonneg (L ℓ : ℕ) (z : ℤ) : 0 ≤ prefR L ℓ z :=
  mul_nonneg (Int.emod_nonneg _ (by positivity)) (by positivity)

/-- The rests have `L` bits. -/
theorem prefR_lt {L ℓ : ℕ} (h : ℓ ≤ L) (z : ℤ) : prefR L ℓ z < 2 ^ L := by
  have hmod : z % 2 ^ ℓ < 2 ^ ℓ := Int.emod_lt_of_pos _ (by positivity)
  rw [prefR, ← Nat.add_sub_cancel' h, pow_add, Nat.add_sub_cancel' h]
  exact mul_lt_mul_of_pos_right hmod (by positivity)

/-- The prefix of a natural number is the quotient of natural numbers. -/
theorem prefQ_natCast (ℓ z : ℕ) : prefQ ℓ (z : ℤ) = ((z / 2 ^ ℓ : ℕ) : ℤ) := by
  simp [prefQ]











/-! ## The lists of the prefixes and of the rests -/

/-- One step on the list of the prefixes. -/
theorem zipWith_shiftQ {L ℓ : ℕ} (h : ℓ + 1 ≤ L) (Z : List ℤ) :
    List.zipWith (shiftQ (2 ^ L)) (Z.map (prefQ (ℓ + 1))) (Z.map (prefR L (ℓ + 1))) =
      Z.map (prefQ ℓ) := by
  rw [List.zipWith_map, List.zipWith_self]
  exact List.map_congr_left fun z _ => (pref_step h z).1.symm

/-- One step on the list of the rests. -/
theorem map_shiftR {L ℓ : ℕ} (h : ℓ + 1 ≤ L) (Z : List ℤ) :
    (Z.map (prefR L (ℓ + 1))).map (shiftR (2 ^ L)) = Z.map (prefR L ℓ) := by
  rw [List.map_map]
  exact List.map_congr_left fun z _ => (pref_step h z).2.symm

/-- At the top level the rests are the numbers themselves. -/
theorem map_prefR_start {L : ℕ} {Z : List ℤ} (h : ∀ z ∈ Z, 0 ≤ z ∧ z < 2 ^ L) :
    Z.map (prefR L L) = Z := by
  conv_rhs => rw [← List.map_id Z]
  exact List.map_congr_left fun z hz => prefR_start (h z hz).1 (h z hz).2

end ThreeSumApsp

end
end

section


/-!
# Negative Triangle from Exact Triangle, on lists of integers

For Theorem 21(b), after [VW13, Proposition 3.4]: whether a triangle has negative weight is
expressed by O(log U) equations between binary prefixes of the shifted weights.

* The weights in `[-U, U]` are shifted to the natural numbers `x = w(a,b) + U`, `y = w(b,c) + U`,
  `v = 2U - w(a,c)`, so that a triangle is negative exactly if `x + y < v`.  The routine computes
  the prefixes `⌊z/2^ℓ⌋` (`prefQ`) of all the numbers `2x`, `2y`, `2v`, which are at most `6U`, at
  once (`negStart`, `bounds_of_mem_negStart`, `zipWith_shiftQ`, `map_shiftR`).
* For each level `ℓ` and for `e = 2` and `e = 3` the reduction makes the instance of Exact Triangle
  with the weights `⌊2x/2^ℓ⌋`, `⌊2y/2^ℓ⌋` and `e - ⌊2v/2^ℓ⌋` (`negThird`, `triOf_level`).  There is
  a negative triangle if and only if one of these instances, at a level `ℓ < L` where `3U < 2^L`,
  has a zero triangle (`hasNegativeTriangle_iff_exists_level`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The instances of the levels -/

/-- At the top level the prefixes are zero. -/
theorem map_prefQ_start {L : ℕ} {Z : List ℤ} (h : ∀ z ∈ Z, 0 ≤ z ∧ z < 2 ^ L) :
    Z.map (prefQ L) = affL 0 0 Z :=
  List.map_congr_left fun z hz => by simp [prefQ_start (h z hz).1 (h z hz).2]











section Bounded

variable {n U : ℕ} {AB BC AC : List ℤ}

/-- The numbers of the start are between 0 and `6U`. -/
theorem bounds_of_mem_negStart (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :
    ∀ z ∈ negStart U AB BC AC, 0 ≤ z ∧ z ≤ 6 * (U : ℤ) := by
  intro z hz
  simp only [negStart, affL, List.mem_append, List.mem_map] at hz
  rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · have := abs_le.1 (hAB x hx); omega
  · have := abs_le.1 (hBC x hx); omega
  · have := abs_le.1 (hAC x hx); omega

/-- The numbers of the third list are at most `6U` in absolute value. -/
theorem abs_le_of_mem_negThird (hU : 1 ≤ U) (hAC : AbsLe AC U) (ℓ : ℕ) {e : ℤ}
    (he : e = 2 ∨ e = 3) : AbsLe (negThird U ℓ e AC) (6 * U) := by
  intro x hx
  simp only [negThird, affL, List.map_map, List.mem_map, Function.comp] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hwU := abs_le.1 (hAC w hw)
  have hv : 0 ≤ -2 * w + 4 * (U : ℤ) := by omega
  have hlow := prefQ_nonneg hv ℓ
  have hhigh := prefQ_le hv ℓ
  rcases he with rfl | rfl <;> exact abs_le.2 ⟨by omega, by omega⟩

/-- The prefix of twice a natural number that is written as an integer. -/
private theorem prefQ_two_mul {x : ℤ} (hx : 0 ≤ x) (ℓ : ℕ) :
    prefQ ℓ (2 * x) = ((2 * x.toNat / 2 ^ ℓ : ℕ) : ℤ) := by
  rw [← prefQ_natCast, Nat.cast_mul, Int.toNat_of_nonneg hx, Nat.cast_ofNat]

/-- An entry of a matrix to whose entries a function has been applied. -/
private theorem getD_map_entry {l : List ℤ} (hl : l.length = n * n) (f : ℤ → ℤ) (a b : Fin n) :
    (l.map f).getD (a * n + b) 0 = f (l.getD (a * n + b) 0) :=
  List.getD_map_of_lt f (hl ▸ Nat.mul_add_lt_mul a.isLt b.isLt) 0 0

/-- The instance made of the lists of the level `ℓ` is the instance of the reduction. -/
theorem triOf_level (lAB : AB.length = n * n) (lBC : BC.length = n * n) (lAC : AC.length = n * n)
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) (ℓ : ℕ) (e : ℤ) :
    triOf n ((affL 2 (2 * U) AB).map (prefQ ℓ)) ((affL 2 (2 * U) BC).map (prefQ ℓ))
        (negThird U ℓ e AC) =
      (triOf n AB BC AC).mapWeights (Theorem21.negToExact U ℓ e) := by
  have hU : (0 : ℤ) ≤ U := Int.natCast_nonneg U
  simp only [triOf, TriangleInstance.mapWeights, Theorem21.negToExact, negThird, affL, List.map_map]
  congr 1 <;> funext a b
  · have hw := abs_le.1 (AbsLe.abs_getD_le hU hAB (a * n + b))
    rw [getD_map_entry lAB, Function.comp_apply, ← prefQ_two_mul (by omega)]
    exact congrArg _ (by ring)
  · have hw := abs_le.1 (AbsLe.abs_getD_le hU hBC (a * n + b))
    rw [getD_map_entry lBC, Function.comp_apply, ← prefQ_two_mul (by omega)]
    exact congrArg _ (by ring)
  · have hw := abs_le.1 (AbsLe.abs_getD_le hU hAC (a * n + b))
    rw [getD_map_entry lAC, ← prefQ_two_mul (by omega)]
    simp only [Function.comp_apply]
    rw [show -2 * AC.getD (a * n + b) 0 + 4 * (U : ℤ) = 2 * (2 * U - AC.getD (a * n + b) 0) by ring]
    ring

/-- **Negative Triangle by prefixes.**  If `3U < 2^L`, then there is a negative triangle if and only
if, at one of the levels `ℓ < L` and for `e = 2` or `e = 3`, the instance made of the prefixes has a
zero triangle. -/
theorem hasNegativeTriangle_iff_exists_level {L : ℕ} (lAB : AB.length = n * n)
    (lBC : BC.length = n * n) (lAC : AC.length = n * n) (hAB : AbsLe AB U) (hBC : AbsLe BC U)
    (hAC : AbsLe AC U) (hL : 3 * U < 2 ^ L) :
    (triOf n AB BC AC).HasNegativeTriangle ↔ ∃ ℓ < L, ∃ e : ℤ, (e = 2 ∨ e = 3) ∧
      (triOf n ((affL 2 (2 * U) AB).map (prefQ ℓ)) ((affL 2 (2 * U) BC).map (prefQ ℓ))
        (negThird U ℓ e AC)).HasZeroTriangle := by
  simp only [triOf_level lAB lBC lAC hAB hBC hAC]
  exact Theorem21.hasNegativeTriangle_iff _ (triOf_bounded hAB hBC hAC) hL

end Bounded

end ThreeSumApsp.Spec

end
end

section


/-!
# Two loops over arrays for the reduction from Negative Triangle to Exact Triangle

[VW13, Theorem 3.3] in the form needed for Theorem 21(b).  The reduction compares
the binary prefixes of shifted weights; the two loops of this file shift the weights and compute the
prefixes, one more bit at a time.

affine(len, src, m, c, dst) writes m · src[i] + c to dst[i] for i < len, in at most 20 len + 6
steps (`affine_meets`).  prefDown(len, q, r, P) makes one step of the computation of the prefixes on
the arrays q and r: it appends the next bit to q[i] and removes it from r[i], for i < len, in at
most 38 len + 6 steps (`prefDown_meets`).  For prefDown the memory after j rounds is written down
(`prefMem`), `prefDownRound_spec` says what one round does, and the loop rule does the rest.  For
m = ±1 and a list that is bounded by U, `affine_meets_of_absLe` has the side conditions in terms
of U.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ### The locals of affine -/

namespace Aff














end Aff





/-! ### The locals of prefDown -/

namespace PrefDown














end PrefDown














/-- **affine** writes the list of the numbers m x + c, for x in the list at src, to dst, and changes
nothing else. -/
theorem affine_meets {p : ℕ} (hp : P[p]? = some affineBody) {μ : ℕ → ℤ} {src dst : ℕ} {m c : ℤ}
    {l : List ℤ} (hl : Seg μ src l) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src + l.length ≤ lim.space) (hdst : dst + l.length ≤ lim.space)
    (hsep : src + l.length ≤ dst ∨ dst + l.length ≤ src)
    (hb : ∀ x ∈ l, |m * x| ≤ lim.word ∧ |m * x + c| ≤ lim.word) :
    Meets lim P p d [l.length, src, m, c, dst] μ (20 * l.length + 6) fun _ μ' =>
      Seg μ' dst (affL m c l) ∧ SameOutside μ μ' dst l.length := by
  refine .of_body hp ?_
  simp only [affineBody, Aff.Len, Aff.Src, Aff.Factor, Aff.Shift, Aff.Dst, Aff.Idx]
  refine Ends.pass (fun i => m * l.getD i 0 + c) (fun j hj => ?_) ?_ hw hdst rfl rfl
  · -- round j reads src[j], which lies outside the cells that are written
    have hread : wrote μ dst (fun i => m * l.getD i 0 + c) j (src + j) = l[j] :=
      (wrote_rest (by omega)).trans (hl j hj)
    obtain ⟨hfits, haddr⟩ := Limits.addr_of_lt hw (x := src + j) (by omega)
    push_cast at hfits haddr
    obtain ⟨hprod, hsum⟩ := hb _ (List.getElem_mem hj)
    have hsrcLoc : frame [(l.length : ℤ), src, m, c, dst] 1 = src := rfl
    have hfactor : frame [(l.length : ℤ), src, m, c, dst] 2 = m := rfl
    have hshift : frame [(l.length : ℤ), src, m, c, dst] 3 = c := rfl
    simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
      Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
      reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one, hsrcLoc, hfactor, hshift,
      toNat_natCast_add_natCast, hread, List.getD_eq_getElem _ _ hj]
    exact ⟨⟨⟨haddr, hfits⟩, hprod⟩, hsum⟩
  · dsimp only
    exact ⟨seg_wrote_map (fun x => m * x + c) l, sameOutside_wrote le_rfl⟩

/-! ### prefDown -/






section prefMem

variable {μ : ℕ → ℤ} {q r : ℕ} {Pw : ℤ} {Q R : List ℤ} {j : ℕ}

/-- A cell of q that has made its step. -/
private theorem prefMem_q_done (hsep : q + Q.length ≤ r ∨ r + Q.length ≤ q) (hj : j ≤ Q.length)
    {i : ℕ} (hi : i < j) :
    prefMem μ q r Pw Q R j (q + i) = shiftQ Pw (Q.getD i 0) (R.getD i 0) :=
  (wrote_rest (by omega)).trans (wrote_done hi)

/-- A cell of r that has made its step. -/
private theorem prefMem_r_done {i : ℕ} (hi : i < j) :
    prefMem μ q r Pw Q R j (r + i) = shiftR Pw (R.getD i 0) :=
  wrote_done hi

/-- A cell that has not been written (yet). -/
private theorem prefMem_rest {a : ℕ} (hq : a < q ∨ q + j ≤ a) (hr : a < r ∨ r + j ≤ a) :
    prefMem μ q r Pw Q R j a = μ a :=
  (wrote_rest hr).trans (wrote_rest hq)

/-- What round j writes. -/
private theorem prefMem_succ (hsep : q + Q.length ≤ r ∨ r + Q.length ≤ q) (hj : j < Q.length) :
    Function.update (Function.update (prefMem μ q r Pw Q R j) (q + j)
      (shiftQ Pw (Q.getD j 0) (R.getD j 0))) (r + j) (shiftR Pw (R.getD j 0)) =
        prefMem μ q r Pw Q R (j + 1) := by
  unfold prefMem
  rw [update_wrote (by omega), wrote_succ, wrote_succ]

end prefMem















/-- **One round of prefDown** makes the step on the pair (q[j], r[j]) and leaves 2 r[j] in Twice. -/
private theorem prefDownRound_spec {μ : ℕ → ℤ} {q r : ℕ} {Pw : ℤ} {Q R : List ℤ}
    (C : PrefPre lim μ q r Pw Q R) {j : ℕ} (hj : j < Q.length) (s : ℤ) :
    Ends lim P d prefDownRound ⟨frame [Q.length, q, r, Pw, j, s], prefMem μ q r Pw Q R j⟩
      prefDownRound.blockCost fun σ' =>
        σ' = ⟨frame [Q.length, q, r, Pw, j, 2 * R.getD j 0], prefMem μ q r Pw Q R (j + 1)⟩ := by
  have hlen := C.len
  have hw := C.space
  have hq := C.inQ
  have hr := C.inR
  have hsep := C.apart
  have h2 := C.two_le
  have hreadQ : prefMem μ q r Pw Q R j (q + j) = Q.getD j 0 :=
    (prefMem_rest (by omega) (by omega)).trans (C.segQ.getD hj 0)
  have hreadR : prefMem μ q r Pw Q R j (r + j) = R.getD j 0 :=
    (prefMem_rest (by omega) (by omega)).trans (C.segR.getD (hlen ▸ hj) 0)
  obtain ⟨hQ2, hQ3⟩ := C.fitsQ _ (List.getD_eq_getElem Q 0 hj ▸ List.getElem_mem hj)
  obtain ⟨hR2, hR3⟩ :=
    C.fitsR _ (List.getD_eq_getElem R 0 (hlen ▸ hj) ▸ List.getElem_mem (hlen ▸ hj))
  have hnext := prefMem_succ (μ := μ) (Pw := Pw) (R := R) hsep hj
  -- from here on x = q[j] and y = r[j]
  generalize Q.getD j 0 = x at hreadQ hQ2 hQ3 hnext
  generalize R.getD j 0 = y at hreadR hR2 hR3 hnext ⊢
  rw [abs_mul, abs_two] at hQ2 hR2
  rw [abs_le] at hQ3 hR3
  unfold prefDownRound
  -- Twice := 2 * mem[ArrR + Idx]
  refine Ends.setToThen (2 * y) ?_ (by simp [Limits.Addr, abs_le, hreadR]; omega)
  -- if Twice < Power
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
  · have hc' : 2 * y < Pw := by simpa using hc
    rw [shiftQ, shiftR, if_pos hc', if_pos hc'] at hnext
    -- mem[ArrQ + Idx] := 2 * mem[ArrQ + Idx]
    refine Ends.storeToThen (q + j) (2 * x) ?_
      (by simp [Limits.Addr, abs_le, hreadQ]; omega)
    -- mem[ArrR + Idx] := Twice
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (r + j) (2 * y) ?_ ?_ ?_);
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
    exact by rw [hnext]; rfl
  · have hc' : ¬ 2 * y < Pw := by simpa using hc
    rw [shiftQ, shiftR, if_neg hc', if_neg hc'] at hnext
    -- mem[ArrQ + Idx] := 2 * mem[ArrQ + Idx] + 1
    refine Ends.storeToThen (q + j) (2 * x + 1) ?_
      (by simp [Limits.Addr, abs_le, hreadQ]; omega)
    -- mem[ArrR + Idx] := Twice - Power
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.storeToThen (r + j) (2 * y - Pw) ?_ ?_ ?_);
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
    exact by rw [hnext]; rfl

/-- **prefDown** makes one step on every pair (q[i], r[i]), and changes nothing else. -/
theorem prefDown_meets {p : ℕ} (hp : P[p]? = some prefDownBody) {μ : ℕ → ℤ} {q r : ℕ} {Pw : ℤ}
    {Q R : List ℤ} (C : PrefPre lim μ q r Pw Q R) :
    Meets lim P p d [Q.length, q, r, Pw] μ (38 * Q.length + 6) fun _ μ' =>
      Seg μ' q (List.zipWith (shiftQ Pw) Q R) ∧ Seg μ' r (R.map (shiftR Pw)) ∧
        ∀ a, (a < q ∨ q + Q.length ≤ a) → (a < r ∨ r + Q.length ≤ a) → μ' a = μ a := by
  refine .of_body hp ?_
  have hlen := C.len
  have hsep := C.apart
  have hfits : (Q.length : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (Nat.le_add_left _ q).trans C.inQ) C.space
  refine Ends.forShape (fun j s μ' => ⟨frame [Q.length, q, r, Pw, j, s], μ'⟩)
    (fun j μ' => μ' = prefMem μ q r Pw Q R j) Q.length prefDownRound.blockCost 0
    (by rw [prefMem, wrote_zero, wrote_zero]) ?round ?done
    (first := by
      rw [update_frame_setLocal]
      exact congrArg (State.mk · μ) (frame_append_zeros _ 1).symm)
    (hT := by simp [prefDownRound]; omega)
  case round =>
    rintro j s _ hj rfl
    exact (prefDownRound_spec C hj s).mono le_rfl fun _ h => ⟨_, _, h, rfl⟩
  case done =>
    rintro s _ rfl
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun a ha hb => prefMem_rest ha hb⟩
    · have hi' : i < Q.length := by simp at hi; omega
      change prefMem μ q r Pw Q R Q.length (q + i) = _
      rw [prefMem_q_done hsep le_rfl hi', List.getElem_zipWith, List.getD_eq_getElem _ _ hi',
        List.getD_eq_getElem _ _ (hlen ▸ hi')]
    · have hi' : i < Q.length := by simp at hi; omega
      change prefMem μ q r Pw Q R Q.length (r + i) = _
      rw [prefMem_r_done hi', List.getElem_map, List.getD_eq_getElem _ _ (hlen ▸ hi')]

/-! ## affine with the factor ± 1 on a list with bounded entries -/































end Light.Sec3

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











/-- The number 1 means yes. -/
theorem flag_eq_one_iff {p : Prop} : flag p = 1 ↔ p := by
  by_cases h : p
  · exact iff_of_true (flag_of h) h
  · exact iff_of_false (by rw [flag_of_not h]; decide) h

/-- Equivalent questions have the same answer. -/
theorem flag_congr {p q : Prop} (h : p ↔ q) : flag p = flag q := by
  rw [propext h]







end ThreeSumApsp

end
end

section


/-!
# Negative Triangle from Exact Triangle, as a host

[VW13, Theorem 3.3] in the form needed for Theorem 21(b): whether an instance with weights in
[−U, U] has a negative triangle is decided by asking O(log U) times whether there is a zero
triangle, each time after changing the weights, edge by edge, to numbers of absolute value O(U).

nt(n, U, ab, bc, ac, fr) computes L, the least number with 2^L > 6U, writes the shifted and doubled
weights 2(w(a,b) + U), 2(w(b,c) + U), 2(2U − w(a,c)) into an array r of 3n² cells, and zeros into an
array q of 3n² cells.  Then it makes L rounds.  A round moves one more bit of every number from r to
q (prefDown), so that q holds the prefixes of the level ℓ = L − 1, L − 2, …, 0; then, for e = 2 and
for e = 3, it writes e minus the prefixes of the third matrix to an array of n² cells and asks the
solver of Exact Triangle.  The answer is 1 if one of the 2L answers is 1.

The text is cut into parts, and each part has its lemma: `NegHost.init_spec`, `pow_spec`,
`fill_spec`, `probe_spec` (one question), `round_spec`, `rounds_spec`; `NegHost.nt_spec` puts them
together, and `isHost_nt` is the result.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The text -/

namespace NegHost












































end NegHost

open NegHost
































































private theorem lt_two_pow_ntLevels (U : ℕ) : 6 * U < 2 ^ ntLevels U :=
  Nat.lt_pow_succ_log_self (by norm_num) _

private theorem two_pow_ntLevels_le {U : ℕ} (hU : 1 ≤ U) : 2 ^ ntLevels U ≤ 12 * U := by
  have := Nat.pow_log_le_self 2 (show 6 * U ≠ 0 by omega)
  rw [ntLevels, pow_succ]
  omega

/-! ## The local variables and the hypotheses -/

namespace NegHost




















variable {P₀ R' : Program} {p pAff pDown : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {lim : Limits}
  {d : ℕ} {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ}

/-- The arithmetic facts of the hypotheses as one conjunction: what the limits allow, and that the
three matrices have n² ≥ 1 entries each and lie below the free pointer. -/
private theorem Ctx.places (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) :
    ((lim.space : ℤ) ≤ lim.word ∧ 24 * (x.U : ℤ) + 8 + (r x.n (6 * x.U)).word ≤ lim.word ∧
      fr + (7 * (x.n * x.n) + (r x.n (6 * x.U)).cells) ≤ lim.space ∧
      d + ((r x.n (6 * x.U)).depth + 1) ≤ lim.depth) ∧ 1 ≤ x.n * x.n ∧
      (x.AB.length = x.n * x.n ∧ x.BC.length = x.n * x.n ∧ x.AC.length = x.n * x.n) ∧
      x.ab + x.n * x.n ≤ fr ∧ x.bc + x.n * x.n ≤ fr ∧ x.ac + x.n * x.n ≤ fr :=
  ⟨⟨C.ok.space, by exact_mod_cast C.ok.word, C.ok.cells, C.ok.depth⟩,
    Nat.mul_pos C.pre.n_pos C.pre.n_pos, ⟨C.pre.lenAB, C.pre.lenBC, C.pre.lenAC⟩, C.pre.belowAB,
    C.pre.belowBC, C.pre.belowAC⟩

/-- **affine** as a procedure, for a source and a destination that lie apart, below the free pointer
of the solver. -/
private theorem Ctx.affine_meets (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) {μ' : ℕ → ℤ}
    {l : List ℤ} {src dst : ℕ} {m c : ℤ} (hl : Seg μ' src l)
    (hplace : src + l.length ≤ fr + 7 * (x.n * x.n) ∧ dst + l.length ≤ fr + 7 * (x.n * x.n) ∧
      (src + l.length ≤ dst ∨ dst + l.length ≤ src))
    (hfits : ∀ w ∈ l, |m * w| ≤ lim.word ∧ |m * w + c| ≤ lim.word) :
    Meets lim (P₀ ++ R') pAff (d + 1) [l.length, src, m, c, dst] μ' (20 * l.length + 6)
      fun _ μ'' => Seg μ'' dst (affL m c l) ∧ SameOutside μ' μ'' dst l.length := by
  have hplaces := C.places
  exact Sec3.affine_meets C.aff hl C.ok.space (by omega) (by omega) hplace.2.2 hfits

/-! ## The beginning -/

/-- **The beginning of nt** sets the sizes and the addresses. -/
private theorem init_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d ntInit ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ ntInit.blockCost
      fun σ' => σ' = ⟨frame (locals x fr 1 0 0 0 0), μ⟩ := by
  have hplaces := C.places
  have hsquare : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
  unfold ntInit
  -- Cells := Verts * Verts ; Bound6 := 6 * Bound
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
    (refine
        Light.Ends.setToThen
          (6 * x.U : ℕ)
            -- PreBC := PreAB + Cells ; PreAC := PreBC + Cells
            
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
  -- PreBC := PreAB + Cells ; PreAC := PreBC + Cells
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
            -- RestAB := PreAC + Cells ; RestBC := RestAB + Cells ; RestAC := RestBC + Cells
            
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
  -- RestAB := PreAC + Cells ; RestBC := RestAB + Cells ; RestAC := RestBC + Cells
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (fr + 3 * (x.n * x.n) : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (fr + 4 * (x.n * x.n) : ℕ) ?_ ?_ ?_);
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
          (fr + 5 * (x.n * x.n) : ℕ)
            -- Third := RestAC + Cells ; SolverFree := Third + Cells ; Cells3 := 3 * Cells
            
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
  -- Third := RestAC + Cells ; SolverFree := Third + Cells ; Cells3 := 3 * Cells
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (fr + 6 * (x.n * x.n) : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (fr + 7 * (x.n * x.n) : ℕ) ?_ ?_ ?_);
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
          (3 * (x.n * x.n) : ℕ)
            -- Power := 1 ; Levels := 0
            
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
  -- Power := 1 ; Levels := 0
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
  rfl





/-- **The loop that doubles** computes the number L of levels and 2^L. -/
private theorem pow_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d ntPow ⟨frame (locals x fr 1 0 0 0 0), μ⟩ (14 * ntLevels x.U + 6)
      fun σ' => σ' = ⟨frame (locals x fr (2 ^ ntLevels x.U : ℕ) (ntLevels x.U) 0 0 0), μ⟩ := by
  have hplaces := C.places
  have hL := two_pow_ntLevels_le C.pre.U_pos
  -- while Power ≤ Bound6: Power := 2 * Power ; Levels := Levels + 1
  refine Ends.whileBlock (PowInv x μ fr) (ntLevels x.U) (by simp [PowInv]) ?round ?done
    (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hpow : 2 ^ (i + 1) ≤ 2 ^ ntLevels x.U := Nat.pow_le_pow_right (by norm_num) hi
    have hlt : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
    rw [pow_succ'] at hpow hlt
    generalize hpw : 2 ^ i = pw at hpow hlt ⊢
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, by (((try have := Light.Std.space_le (by assumption)));
                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      by simp [PowInv, pow_succ', hpw, update_frame_setLocal, locals]⟩
  case done =>
    rintro _ rfl
    have hlt := lt_two_pow_ntLevels x.U
    generalize 2 ^ ntLevels x.U = pw at hL hlt ⊢
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, rfl⟩

/-! ## The memory -/









private theorem length_negStart {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr) :
    (negStart x.U x.AB x.BC x.AC).length = 3 * (x.n * x.n) := by
  simp only [negStart, List.length_append, length_affL, hpre.lenAB, hpre.lenBC, hpre.lenAC]
  omega

/-- The numbers at the start are between 0 and 6U, and below 2^L. -/
private theorem negStart_range {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr) :
    ∀ z ∈ negStart x.U x.AB x.BC x.AC, 0 ≤ z ∧ z ≤ 6 * (x.U : ℤ) ∧ z < 2 ^ ntLevels x.U := by
  intro z hz
  obtain ⟨h0, h1⟩ := bounds_of_mem_negStart hpre.leAB hpre.leBC hpre.leAC z hz
  have h2 : ((6 * x.U : ℕ) : ℤ) < ((2 ^ ntLevels x.U : ℕ) : ℤ) := by
    exact_mod_cast lt_two_pow_ntLevels x.U
  push_cast at h2
  exact ⟨h0, h1, by omega⟩

/-- The three shifted and doubled matrices, one after the other, are the array r at the start. -/
private theorem seg_negStart (hpre : x.Pre μ fr) {μ' : ℕ → ℤ} {a : ℕ}
    (h1 : Seg μ' (a + 3 * (x.n * x.n)) (affL 2 (2 * x.U) x.AB))
    (h2 : Seg μ' (a + 4 * (x.n * x.n)) (affL 2 (2 * x.U) x.BC))
    (h3 : Seg μ' (a + 5 * (x.n * x.n)) (affL (-2) (4 * x.U) x.AC)) :
    Seg μ' (a + 3 * (x.n * x.n)) (negStart x.U x.AB x.BC x.AC) := by
  rw [negStart, seg_append, seg_append]
  simp only [length_affL, hpre.lenAB, hpre.lenBC]
  rw [show a + 3 * (x.n * x.n) + x.n * x.n = a + 4 * (x.n * x.n) by omega,
    show a + 4 * (x.n * x.n) + x.n * x.n = a + 5 * (x.n * x.n) by omega]
  exact ⟨h1, h2, h3⟩

/-- The products and the sums that are formed in the first three calls of affine fit in a word. -/
private theorem fits_of_absLe {l : List ℤ} {U W : ℤ} (hl : AbsLe l U) (hW : 24 * U + 8 ≤ W) :
    (∀ w ∈ l, |2 * w| ≤ W ∧ |2 * w + 2 * U| ≤ W) ∧
      ∀ w ∈ l, |-2 * w| ≤ W ∧ |-2 * w + 4 * U| ≤ W := by
  constructor <;> intro w hw <;> have := abs_le.1 (hl w hw) <;> simp only [abs_le] <;> omega

/-- **The four calls of affine** fill the arrays r and q for the top level. -/
private theorem fill_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) (pw lv rd ans res : ℤ) :
    Ends lim (P₀ ++ R') d (ntFill pAff) ⟨frame (locals x fr pw lv rd ans res), μ⟩
      (120 * (x.n * x.n) + 60) fun σ' => ∃ res' μ',
        σ' = ⟨frame (locals x fr pw lv rd ans res'), μ'⟩ ∧ NtMem x μ fr (ntLevels x.U) μ' := by
  have hpre := C.pre
  have hplaces := C.places
  have hlenZ := length_negStart hpre
  have hZ := negStart_range hpre
  have hW : 24 * (x.U : ℤ) + 8 ≤ lim.word := by omega
  unfold ntFill
  -- Res := pAff(Cells, MatAB, 2, 2 * Bound, RestAB)
  refine Ends.callToThen (C.affine_meets (m := 2) (c := 2 * x.U) (dst := fr + 3 * (x.n * x.n))
    hpre.segAB (by omega) (fits_of_absLe hpre.leAB hW).1) ?_
    (ha := by (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hpre.lenAB] <;> omega))) (hT := by simp [hpre.lenAB]; omega)
  rintro r₁ μ₁ ⟨s₁, o₁⟩
  -- Res := pAff(Cells, MatBC, 2, 2 * Bound, RestBC)
  refine Ends.callToThen (C.affine_meets (m := 2) (c := 2 * x.U) (dst := fr + 4 * (x.n * x.n))
    hpre.segBC.keep (by omega) (fits_of_absLe hpre.leBC hW).1) ?_
    (ha := by (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hpre.lenBC] <;> omega))) (hT := by simp [hpre.lenAB, hpre.lenBC]; omega)
  rintro r₂ μ₂ ⟨s₂, o₂⟩
  -- Res := pAff(Cells, MatAC, 0 - 2, 4 * Bound, RestAC)
  refine Ends.callToThen (C.affine_meets (m := -2) (c := 4 * x.U) (dst := fr + 5 * (x.n * x.n))
    hpre.segAC.keep (by omega) (fits_of_absLe hpre.leAC hW).2) ?_ (ha := by (((try have := Light.Std.space_le (by assumption)));
                                                                              ((try have := Light.Std.const_le (by assumption)));
                                                                              (simp [Light.Limits.Addr, abs_le, -abs_mul, hpre.lenAC] <;> omega)))
    (hT := by simp [hpre.lenAB, hpre.lenBC, hpre.lenAC]; omega)
  rintro r₃ μ₃ ⟨s₃, o₃⟩
  have sZ : Seg μ₃ (fr + 3 * (x.n * x.n)) (negStart x.U x.AB x.BC x.AC) :=
    seg_negStart hpre s₁.keep s₂.keep s₃
  -- Res := pAff(Cells3, RestAB, 0, 0, PreAB)
  refine Ends.callTo (C.affine_meets (m := 0) (c := 0) (dst := fr) sZ (by omega)
    fun w _ => by simp; omega) ?_ (ha := by (((try have := Light.Std.space_le (by assumption)));
                                              ((try have := Light.Std.const_le (by assumption)));
                                              (simp [Light.Limits.Addr, abs_le, -abs_mul, hlenZ] <;> omega)))
    (hT := by simp [hpre.lenAB, hpre.lenBC, hpre.lenAC, hlenZ]; omega)
  rintro r₄ μ₄ ⟨s₄, o₄⟩
  refine ⟨r₄, μ₄, rfl, ?_, ?_, fun c hc => ?_⟩
  · rw [map_prefQ_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]
    exact s₄
  · rw [map_prefR_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]
    exact sZ.keep
  · ((try refine Light.SameOn.cell ?_); (intro apspMacro_98731_0 apspMacro_98731_1);
       (first
         |
           ((((repeat
                     (((with_reducible
                             rename Light.SameOn _ _ _ => apspMacro_98731_2));
                       ((try
                             have :=
                               apspMacro_98731_2 apspMacro_98731_0 (by omega)));
                       (revert apspMacro_98731_2)));
                 (intros);
                 (try simp only [Function.update_apply, Light.wrote] at *)));
             (omega))
         |
           ((simp [] at apspMacro_98731_1);
             (((repeat
                     (((with_reducible
                             rename Light.SameOn _ _ _ => apspMacro_98731_3));
                       ((try
                             have :=
                               apspMacro_98731_3 apspMacro_98731_0 (by omega)));
                       (revert apspMacro_98731_3)));
                 (intros);
                 (try simp only [Function.update_apply, Light.wrote] at *)));
             (omega))
         |
           ((((repeat
                     (((with_reducible
                             rename Light.SameOn _ _ _ => apspMacro_98731_4));
                       ((try
                             have :=
                               apspMacro_98731_4 apspMacro_98731_0 (by omega)));
                       (revert apspMacro_98731_4)));
                 (intros);
                 (try simp only [Function.update_apply, Light.wrote] at *)));
             (fail
                 "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                           SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                           its condition K x does not follow from the hypotheses."))))

/-! ## One question -/












/-- The prefixes are between 0 and 6U. -/
private theorem prefQ_range (hpre : x.Pre μ fr) (ℓ : ℕ) {z : ℤ}
    (hz : z ∈ negStart x.U x.AB x.BC x.AC) :
    0 ≤ prefQ ℓ z ∧ prefQ ℓ z ≤ 6 * (x.U : ℤ) := by
  obtain ⟨h0, h1⟩ := bounds_of_mem_negStart hpre.leAB hpre.leBC hpre.leAC z hz
  exact ⟨prefQ_nonneg h0 ℓ, (prefQ_le h0 ℓ).trans h1⟩

/-- The three parts of the array q. -/
private theorem seg_parts (hpre : x.Pre μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ}
    (hq : Seg μ' fr ((negStart x.U x.AB x.BC x.AC).map (prefQ ℓ))) :
    Seg μ' fr ((affL 2 (2 * x.U) x.AB).map (prefQ ℓ)) ∧
      Seg μ' (fr + x.n * x.n) ((affL 2 (2 * x.U) x.BC).map (prefQ ℓ)) ∧
      Seg μ' (fr + 2 * (x.n * x.n)) ((affL (-2) (4 * x.U) x.AC).map (prefQ ℓ)) := by
  simp only [negStart, List.map_append] at hq
  rw [seg_append, seg_append] at hq
  simp only [List.length_map, length_affL, hpre.lenAB, hpre.lenBC] at hq
  rwa [show fr + x.n * x.n + x.n * x.n = fr + 2 * (x.n * x.n) by omega] at hq

/-- The question is an instance of Exact Triangle as the task prescribes. -/
private theorem question_pre (hpre : x.Pre μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ} {e : ℤ} (he : e = 2 ∨ e = 3)
    (hq : Seg μ' fr ((negStart x.U x.AB x.BC x.AC).map (prefQ ℓ)))
    (hthird : Seg μ' (fr + 6 * (x.n * x.n)) (negThird x.U ℓ e x.AC)) :
    (question x fr ℓ e).Pre μ' (fr + 7 * (x.n * x.n)) := by
  obtain ⟨hqX, hqY, -⟩ := seg_parts hpre hq
  have hle : ∀ l : List ℤ, (∀ z ∈ l, z ∈ negStart x.U x.AB x.BC x.AC) →
      AbsLe (l.map (prefQ ℓ)) ((6 * x.U : ℕ) : ℤ) := by
    intro l hl y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have := prefQ_range hpre ℓ (hl z hz)
    push_cast
    exact abs_le.2 ⟨by omega, by omega⟩
  have hU := hpre.U_pos
  exact {
    n_pos := hpre.n_pos
    U_pos := by simp only [question]; omega
    lenAB := by simp [question, hpre.lenAB]
    lenBC := by simp [question, hpre.lenBC]
    lenAC := by simp [question, negThird, hpre.lenAC]
    segAB := hqX
    segBC := hqY
    segAC := hthird
    leAB := hle _ fun z hz => by simp [negStart, hz]
    leBC := hle _ fun z hz => by simp [negStart, hz]
    leAC := fun y hy => by
      simp only [question]
      push_cast
      exact abs_le_of_mem_negThird hpre.U_pos hpre.leAC ℓ he y hy
    belowAB := by simp only [question]; omega
    belowBC := by simp only [question]; omega
    belowAC := by simp only [question]; omega }








/-- The arrays q and r and the cells below the free pointer survive a question. -/
private theorem ntMem_of_question (hpre : x.Pre μ fr) {μ₀ μ₁ μ₂ : ℕ → ℤ} {ℓ : ℕ}
    (hm : NtMem x μ fr ℓ μ₀) (h₁ : SameOutside μ₀ μ₁ (fr + 6 * (x.n * x.n)) (x.n * x.n))
    (h₂ : Kept μ₁ μ₂ (fr + 7 * (x.n * x.n))) : NtMem x μ fr ℓ μ₂ := by
  obtain ⟨hq, hr, hk⟩ := hm
  have hlenZ := length_negStart hpre
  exact ⟨hq.keep (by ((try have := hlenZ);
                         (((try refine Light.SameOn.cell ?_);
                             (intro apspMacro_101715_0 apspMacro_101715_1);
                             (first
                               |
                                 ((((repeat
                                           (((with_reducible
                                                   rename Light.SameOn _ _ _ => apspMacro_101715_2));
                                             ((try
                                                   have :=
                                                     apspMacro_101715_2 apspMacro_101715_0
                                                       (by omega)));
                                             (revert apspMacro_101715_2)));
                                       (intros);
                                       (try simp only [Function.update_apply, Light.wrote] at *)));
                                   (omega))
                               |
                                 ((simp [hlenZ] at apspMacro_101715_1);
                                   (((repeat
                                           (((with_reducible
                                                   rename Light.SameOn _ _ _ => apspMacro_101715_3));
                                             ((try
                                                   have :=
                                                     apspMacro_101715_3 apspMacro_101715_0
                                                       (by omega)));
                                             (revert apspMacro_101715_3)));
                                       (intros);
                                       (try simp only [Function.update_apply, Light.wrote] at *)));
                                   (omega))
                               |
                                 ((((repeat
                                           (((with_reducible
                                                   rename Light.SameOn _ _ _ => apspMacro_101715_4));
                                             ((try
                                                   have :=
                                                     apspMacro_101715_4 apspMacro_101715_0
                                                       (by omega)));
                                             (revert apspMacro_101715_4)));
                                       (intros);
                                       (try simp only [Function.update_apply, Light.wrote] at *)));
                                   (fail
                                       "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                 SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                 its condition K x does not follow from the hypotheses."))))))), hr.keep (by ((try have := hlenZ);
                                                                                                                               (((try refine Light.SameOn.cell ?_);
                                                                                                                                   (intro apspMacro_101748_0 apspMacro_101748_1);
                                                                                                                                   (first
                                                                                                                                     |
                                                                                                                                       ((((repeat
                                                                                                                                                 (((with_reducible
                                                                                                                                                         rename Light.SameOn _ _ _ => apspMacro_101748_2));
                                                                                                                                                   ((try
                                                                                                                                                         have :=
                                                                                                                                                           apspMacro_101748_2 apspMacro_101748_0
                                                                                                                                                             (by omega)));
                                                                                                                                                   (revert apspMacro_101748_2)));
                                                                                                                                             (intros);
                                                                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                                                                         (omega))
                                                                                                                                     |
                                                                                                                                       ((simp [hlenZ] at apspMacro_101748_1);
                                                                                                                                         (((repeat
                                                                                                                                                 (((with_reducible
                                                                                                                                                         rename Light.SameOn _ _ _ => apspMacro_101748_3));
                                                                                                                                                   ((try
                                                                                                                                                         have :=
                                                                                                                                                           apspMacro_101748_3 apspMacro_101748_0
                                                                                                                                                             (by omega)));
                                                                                                                                                   (revert apspMacro_101748_3)));
                                                                                                                                             (intros);
                                                                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                                                                         (omega))
                                                                                                                                     |
                                                                                                                                       ((((repeat
                                                                                                                                                 (((with_reducible
                                                                                                                                                         rename Light.SameOn _ _ _ => apspMacro_101748_4));
                                                                                                                                                   ((try
                                                                                                                                                         have :=
                                                                                                                                                           apspMacro_101748_4 apspMacro_101748_0
                                                                                                                                                             (by omega)));
                                                                                                                                                   (revert apspMacro_101748_4)));
                                                                                                                                             (intros);
                                                                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                                                                         (fail
                                                                                                                                             "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                                                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                                                                       its condition K x does not follow from the hypotheses."))))))),
    fun c hc => by ((try refine Light.SameOn.cell ?_);
                     (intro apspMacro_101788_0 apspMacro_101788_1);
                     (first
                       |
                         ((((repeat
                                   (((with_reducible
                                           rename Light.SameOn _ _ _ => apspMacro_101788_2));
                                     ((try
                                           have :=
                                             apspMacro_101788_2 apspMacro_101788_0 (by omega)));
                                     (revert apspMacro_101788_2)));
                               (intros);
                               (try simp only [Function.update_apply, Light.wrote] at *)));
                           (omega))
                       |
                         ((simp [] at apspMacro_101788_1);
                           (((repeat
                                   (((with_reducible
                                           rename Light.SameOn _ _ _ => apspMacro_101788_3));
                                     ((try
                                           have :=
                                             apspMacro_101788_3 apspMacro_101788_0 (by omega)));
                                     (revert apspMacro_101788_3)));
                               (intros);
                               (try simp only [Function.update_apply, Light.wrote] at *)));
                           (omega))
                       |
                         ((((repeat
                                   (((with_reducible
                                           rename Light.SameOn _ _ _ => apspMacro_101788_4));
                                     ((try
                                           have :=
                                             apspMacro_101788_4 apspMacro_101788_0 (by omega)));
                                     (revert apspMacro_101788_4)));
                               (intros);
                               (try simp only [Function.update_apply, Light.wrote] at *)));
                           (fail
                               "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                         SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                         its condition K x does not follow from the hypotheses."))))⟩

/-- **One question** leaves the arrays as they are, and sets Ans to 1 if the instance for the level
ℓ and the exact value e has a zero triangle. -/
private theorem probe_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) {ℓ e : ℕ}
    (he : e = 2 ∨ e = 3) {rd : ℤ} {A : Prop} {σ : State} (hσ : St x μ fr rd (flag A) ℓ σ) :
    Ends lim (P₀ ++ R') d (ntProbe p pAff e) σ (20 * (x.n * x.n) + 29 + T x.n (6 * x.U))
      (St x μ fr rd (flag (A ∨ NtYes x ℓ e)) ℓ) := by
  obtain ⟨res, μ₀, rfl, hm⟩ := hσ
  have hpre := C.pre
  have hplaces := C.places
  have he' : (e : ℤ) = 2 ∨ (e : ℤ) = 3 := by rcases he with rfl | rfl <;> simp
  have hlenV : ((affL (-2) (4 * x.U) x.AC).map (prefQ ℓ)).length = x.n * x.n := by
    simp [hpre.lenAC]
  unfold ntProbe
  -- Res := pAff(Cells, PreAC, 0 - 1, e, Third)
  refine Ends.callToThen (C.affine_meets (m := -1) (c := e) (dst := fr + 6 * (x.n * x.n))
    (seg_parts hpre hm.1).2.2 (by omega) fun w hx => ?_) ?_
    (ha := by (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hlenV] <;> omega))) (hT := by simp [hlenV]; omega)
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    have := prefQ_range hpre ℓ (z := z) (by simp [negStart, hz])
    simp only [abs_le]
    omega
  rintro r₁ μ₁ ⟨hthird, h₁⟩
  rw [hlenV] at h₁
  -- Res := pET(Verts, Bound6, PreAB, PreBC, Third, SolverFree)
  refine Ends.callToThen (C.solver.meets R' (question x fr ℓ e) (fr + 7 * (x.n * x.n))
    (question_pre hpre he' (hm.1.keep (by ((try have := length_negStart hpre);
                                            (((try refine Light.SameOn.cell ?_);
                                                (intro apspMacro_103265_0 apspMacro_103265_1);
                                                (first
                                                  |
                                                    ((((repeat
                                                              (((with_reducible
                                                                      rename Light.SameOn _ _ _ => apspMacro_103265_2));
                                                                ((try
                                                                      have :=
                                                                        apspMacro_103265_2 apspMacro_103265_0
                                                                          (by omega)));
                                                                (revert apspMacro_103265_2)));
                                                          (intros);
                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                      (omega))
                                                  |
                                                    ((simp [length_negStart hpre] at apspMacro_103265_1);
                                                      (((repeat
                                                              (((with_reducible
                                                                      rename Light.SameOn _ _ _ => apspMacro_103265_3));
                                                                ((try
                                                                      have :=
                                                                        apspMacro_103265_3 apspMacro_103265_0
                                                                          (by omega)));
                                                                (revert apspMacro_103265_3)));
                                                          (intros);
                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                      (omega))
                                                  |
                                                    ((((repeat
                                                              (((with_reducible
                                                                      rename Light.SameOn _ _ _ => apspMacro_103265_4));
                                                                ((try
                                                                      have :=
                                                                        apspMacro_103265_4 apspMacro_103265_0
                                                                          (by omega)));
                                                                (revert apspMacro_103265_4)));
                                                          (intros);
                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                      (fail
                                                          "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                    SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                    its condition K x does not follow from the hypotheses.")))))))) hthird)
    { word := by simp only [etTask, question]; omega
      cells := by simp only [etTask, question]; omega
      space := C.ok.space
      depth := by simp only [etTask, question]; omega }) ?_ (by simp [etTask, question])
    (hT := by simp [etTask, question, hlenV]; omega)
  rintro r₂ μ₂ ⟨hres, h₂⟩
  replace hres : r₂ = flag (NtYes x ℓ e) := hres
  have hm₂ := ntMem_of_question hpre hm h₁ h₂
  -- if Res = 1 then Ans := 1
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by simp; omega)
    (by simp [etTask, question, hlenV]; omega)
  · have hc' : r₂ = 1 := by simpa using hc
    refine Ends.setTo 1 ⟨r₂, μ₂, ?_, hm₂⟩ (by simp; omega)
      (by simp [etTask, question, hlenV]; omega)
    rw [flag_of (Or.inr (flag_eq_one_iff.1 (hres ▸ hc')))]
    rfl
  · have hc' : ¬ r₂ = 1 := by simpa using hc
    refine Ends.skip ⟨r₂, μ₂, ?_, hm₂⟩
    rw [flag_congr (show (A ∨ NtYes x ℓ e) ↔ A from
      ⟨fun h => h.resolve_right fun hy => hc' (hres.trans (flag_of hy)), Or.inl⟩)]
    rfl

/-! ## The rounds -/





private theorem ntFound_step (x : TriInst) {L ℓ : ℕ} (h : ℓ < L) :
    ((NtFound x L (ℓ + 1) ∨ NtYes x ℓ 2) ∨ NtYes x ℓ 3) ↔ NtFound x L ℓ := by
  constructor
  · rintro ((⟨ℓ', h1, h2, h3⟩ | h2) | h3)
    · exact ⟨ℓ', by omega, h2, h3⟩
    · exact ⟨ℓ, le_rfl, h, 2, Or.inl rfl, h2⟩
    · exact ⟨ℓ, le_rfl, h, 3, Or.inr rfl, h3⟩
  · rintro ⟨ℓ', h1, h2, e, he, h3⟩
    by_cases hℓ : ℓ' = ℓ
    · subst hℓ
      rcases he with rfl | rfl
      · exact Or.inl (Or.inr h3)
      · exact Or.inr h3
    · exact Or.inl (Or.inl ⟨ℓ', by omega, h2, e, he, h3⟩)

/-- The number of the round can be read and changed. -/
private theorem St.round {rd ans : ℤ} {ℓ : ℕ} {σ : State} (h : St x μ fr rd ans ℓ σ) (rd' : ℤ) :
    σ.loc Round = rd ∧ St x μ fr rd' ans ℓ { σ with loc := Function.update σ.loc Round rd' } := by
  obtain ⟨res, μ', rfl, hm⟩ := h
  exact ⟨rfl, res, μ', by rw [update_frame_setLocal]; rfl, hm⟩

/-- What prefDown needs holds at every level above 0. -/
private theorem down_pre (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ ntLevels x.U) (hm : NtMem x μ fr (ℓ + 1) μ') :
    PrefPre lim μ' fr (fr + 3 * (x.n * x.n)) (2 ^ ntLevels x.U)
      ((negStart x.U x.AB x.BC x.AC).map (prefQ (ℓ + 1)))
      ((negStart x.U x.AB x.BC x.AC).map (prefR (ntLevels x.U) (ℓ + 1))) := by
  have hplaces := C.places
  have hlenZ := length_negStart C.pre
  have hL : ((2 ^ ntLevels x.U : ℕ) : ℤ) ≤ ((12 * x.U : ℕ) : ℤ) := by
    exact_mod_cast two_pow_ntLevels_le C.pre.U_pos
  push_cast at hL
  refine ⟨hm.1, hm.2.1, by simp, C.ok.space, by simp [hlenZ]; omega, by simp [hlenZ]; omega,
    by simp [hlenZ], by omega, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have := prefQ_range C.pre (ℓ + 1) hz
    simp only [abs_le]
    omega
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have h0 := prefR_nonneg (ntLevels x.U) (ℓ + 1) z
    have h1 := prefR_lt hℓ z
    simp only [abs_le]
    omega

/-- **One round**: from the level ℓ + 1 to the level ℓ, and the two questions at the level ℓ. -/
private theorem round_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) {ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ ntLevels x.U) {rd : ℤ} {σ : State}
    (hσ : St x μ fr rd (flag (NtFound x (ntLevels x.U) (ℓ + 1))) (ℓ + 1) σ) :
    Ends lim (P₀ ++ R') d (ntRound p pAff pDown) σ (154 * (x.n * x.n) + 70 + 2 * T x.n (6 * x.U))
      (St x μ fr rd (flag (NtFound x (ntLevels x.U) ℓ)) ℓ) := by
  obtain ⟨res, μ₀, rfl, hm⟩ := hσ
  have hplaces := C.places
  have hlenZ := length_negStart C.pre
  unfold ntRound
  -- Res := pDown(Cells3, PreAB, RestAB, Power)
  refine Ends.callToThen (prefDown_meets C.down (down_pre C hℓ hm)) ?_ (by simp [hlenZ])
    (hT := by simp [hlenZ]; omega)
  rintro r₁ μ₁ ⟨hq, hr, hrest⟩
  rw [zipWith_shiftQ hℓ] at hq
  rw [map_shiftR hℓ] at hr
  have hσ₁ : St x μ fr rd (flag (NtFound x (ntLevels x.U) (ℓ + 1))) ℓ
      ⟨frame (locals x fr (2 ^ ntLevels x.U : ℕ) (ntLevels x.U) rd
        (flag (NtFound x (ntLevels x.U) (ℓ + 1))) r₁), μ₁⟩ :=
    ⟨r₁, μ₁, rfl, hq, hr,
      fun c hc => (hrest c (Or.inl hc) (Or.inl (by omega))).trans (hm.2.2 c hc)⟩
  -- the question for e = 2, then the question for e = 3
  refine Ends.next _ ((probe_spec C (Or.inl rfl) hσ₁).mono le_rfl fun σ₂ hσ₂ => ?_)
    (by simp [hlenZ]; omega)
  refine (probe_spec C (Or.inr rfl) hσ₂).mono (by simp [hlenZ]; omega) fun σ₃ hσ₃ => ?_
  rwa [flag_congr (by simpa using ntFound_step x (Nat.lt_of_succ_le hℓ))] at hσ₃

/-- **The L rounds**: in the end Ans says whether one of the questions at the levels below L was
answered yes. -/
private theorem rounds_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) {res : ℤ} {μ' : ℕ → ℤ}
    (hm : NtMem x μ fr (ntLevels x.U) μ') :
    Ends lim (P₀ ++ R') d (ntRounds p pAff pDown)
      ⟨frame (locals x fr (2 ^ ntLevels x.U : ℕ) (ntLevels x.U) 0 0 res), μ'⟩
      (8 + ntLevels x.U * (154 * (x.n * x.n) + 78 + 2 * T x.n (6 * x.U)))
      (St x μ fr (ntLevels x.U) (flag (NtFound x (ntLevels x.U) 0)) 0) := by
  have hplaces := C.places
  have hL : ((ntLevels x.U : ℕ) : ℤ) ≤ ((12 * x.U : ℕ) : ℤ) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := ntLevels x.U)).le.trans
      (two_pow_ntLevels_le C.pre.U_pos)
  push_cast at hL
  unfold ntRounds
  -- Ans := 0
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
            -- for Round < Levels: the rounds
            
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
  -- for Round < Levels: the rounds
  refine Ends.for (fun t σ => St x μ fr t (flag (NtFound x (ntLevels x.U) (ntLevels x.U - t)))
    (ntLevels x.U - t) σ) (ntLevels x.U) (154 * (x.n * x.n) + 70 + 2 * T x.n (6 * x.U))
    ?start ?round ?done ?bound (by omega) ?time
  case start =>
    refine ⟨res, μ', ?_, hm⟩
    rw [flag_of_not (by rintro ⟨ℓ, h1, h2, -⟩; omega), update_frame_setLocal]
    rfl
  case round =>
    intro t σ ht _ hσ
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ntLevels x.U - t = ℓ + 1 := ⟨ntLevels x.U - t - 1, by omega⟩
    rw [show ntLevels x.U - (t + 1) = ℓ by omega]
    rw [hℓ] at hσ
    refine (round_spec C (by omega) hσ).mono le_rfl fun σ' hσ' => ?_
    exact_mod_cast hσ'.round ((t : ℤ) + 1)
  case done =>
    intro σ _ hσ
    simpa using hσ
  case bound =>
    rintro t _ - - ⟨res', μ'', rfl, -⟩
    exact ⟨trivial, rfl⟩
  case time =>
    simp
    ring_nf
    omega

/-! ## The procedure -/

/-- **nt is correct**, in every program that begins with the solver's program and has the two loops
over arrays. -/
theorem nt_spec (C : Ctx P₀ R' p pAff pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d (ntBody p pAff pDown) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩
      (ntTime T x.n x.U) fun σ' =>
        σ'.loc 0 = flag (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle ∧ Kept μ σ'.mem fr := by
  have hpre := C.pre
  have hrounds : ntLevels x.U * (154 * (x.n * x.n) + 92 + 2 * T x.n (6 * x.U)) =
      ntLevels x.U * (154 * (x.n * x.n) + 78 + 2 * T x.n (6 * x.U)) + 14 * ntLevels x.U := by
    ring
  unfold ntBody ntTime
  -- ntInit
  refine Ends.next _ ((init_spec C).mono le_rfl ?_) (by simp [ntInit]; omega)
  rintro _ rfl
  -- ntPow
  refine Ends.next _ ((pow_spec C).mono le_rfl ?_) (by simp [ntInit]; omega)
  rintro _ rfl
  -- ntFill
  refine Ends.next _ ((fill_spec C _ _ _ _ _).mono le_rfl ?_) (by simp [ntInit]; omega)
  rintro _ ⟨res, μ₁, rfl, hm⟩
  -- ntRounds
  refine Ends.next _ ((rounds_spec C hm).mono le_rfl ?_) (by simp [ntInit]; omega)
  rintro _ ⟨res', μ₂, rfl, hm₂⟩
  -- the result is Ans
  refine Ends.setTo (flag (NtFound x (ntLevels x.U) 0)) ⟨?_, hm₂.2.2⟩ (hT := by
    simp [ntInit]; omega)
  have h3 : 3 * x.U < 2 ^ ntLevels x.U := by have := lt_two_pow_ntLevels x.U; omega
  refine flag_congr ?_
  rw [hasNegativeTriangle_iff_exists_level hpre.lenAB hpre.lenBC hpre.lenAC hpre.leAB hpre.leBC
    hpre.leAC h3]
  exact ⟨fun ⟨ℓ, _, h2, h⟩ => ⟨ℓ, h2, h⟩, fun ⟨ℓ, h2, h⟩ => ⟨ℓ, Nat.zero_le _, h2, h⟩⟩

end NegHost

/-- The need of nt is polynomially bounded if the need of the solver is. -/
theorem polyNeed_ntNeed {r : ℕ → ℕ → Need} (h : PolyNeed r) : PolyNeed (ntNeed r) := by
  unfold ntNeed
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
                  | apply h.word
                  | apply h.cells
                  | apply h.depth
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
                                | apply h.word
                                | apply h.cells
                                | apply h.depth
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
                          | apply h.word
                          | apply h.cells
                          | apply h.depth
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
                  | apply h.word
                  | apply h.cells
                  | apply h.depth
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)))

/-- **Negative Triangle from Exact Triangle**: from every solver of Exact Triangle, the three
procedures affine, prefDown, nt make a solver of Negative Triangle. -/
theorem isHost_nt : IsHost etTask ntTask ntTime ntNeed := by
  refine ⟨fun P p T r hsol => ⟨[affineBody, prefDownBody, ntBody p P.length (P.length + 1)],
    P.length + 2, ntBody p P.length (P.length + 1), by simp, fun R lim d x μ fr hpre hok => ?_⟩,
    fun r => polyNeed_ntNeed⟩
  rw [List.append_assoc]
  exact NegHost.nt_spec ⟨hsol, by simp, by simp, hpre, hok⟩

end Light.Sec3

end
end

section


/-!
# `logU`, the paper's `log U`

`logU u` is `log u`, read as `log 2` for `u < 2`.

* It is positive and nondecreasing, and `log (cu) ≤ log c + log u` for `c ≥ 1`.
* `log (cU) = O(log U)` (`dominated_logU_mul`) and `log (c n^κ) = O(log n)`
  (`dominated_logU_mul_rpow`).
* Along bounds `u(n) ≤ c n^κ` it is `Õ(1)` (`isPowPolylog_logU_of_le`).
-/

public section

namespace ThreeSumApsp

/-- `logU u ≥ log 2`. -/
theorem log_two_le_logU (u : ℝ) : Real.log 2 ≤ logU u :=
  Real.log_le_log two_pos (le_max_right _ _)

/-- `logU u > 0`. -/
theorem logU_pos (u : ℝ) : 0 < logU u :=
  (Real.log_pos one_lt_two).trans_le (log_two_le_logU u)





/-- `log u ≤ logU u` for `u > 0`. -/
theorem log_le_logU {u : ℝ} (hu : 0 < u) : Real.log u ≤ logU u :=
  Real.log_le_log hu (le_max_left _ _)




























/-! ## `logU` of a multiple -/
























/-! ## `logU` along bounds that are polynomial in `n` -/

















end ThreeSumApsp

end
end

section


/-!
# The claim [VW13, Theorem 3.3] in the light language

The arithmetic that turns the time function of the host (`ntTime`, `isHost_nt`) into the bound
C · T(s, 6U) · log U of the claim. The host's own work, O(n² log U), is at most the time of the
solver, because a good time is at least n².
-/

public section

namespace Light.Sec3

open ThreeSumApsp

/-- The number of levels is O(log U). -/
theorem ntLevels_le {U : ℕ} (hU : 1 ≤ U) {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (ntLevels U : ℝ) ≤ 10 * logU u := by
  have hshift : Nat.log 2 (6 * U) ≤ Nat.log 2 U + 3 := by
    calc Nat.log 2 (6 * U) ≤ Nat.log 2 (U * 2 * 2 * 2) := Nat.log_mono_right (by omega)
      _ = Nat.log 2 U + 3 := by
        rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
          Nat.log_mul_base (by norm_num) (by omega)]
  have hfloor : (Nat.log 2 U : ℝ) ≤ Real.logb (2 : ℕ) U := Real.natLog_le_logb U 2
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hmono : Real.log U ≤ logU u :=
    (Real.log_le_log (by linarith) hu).trans (log_le_logU (by linarith))
  have hhalf := Real.one_half_lt_log_two
  have hbase : Real.logb (2 : ℕ) U ≤ 2 * Real.log U := by
    have hlog0 : 0 ≤ Real.log U := Real.log_nonneg hU'
    rw [Real.logb, Nat.cast_ofNat, div_le_iff₀ (by linarith)]
    nlinarith
  have htwo := log_two_le_logU u
  have hlevels : (ntLevels U : ℝ) ≤ (Nat.log 2 U : ℝ) + 4 := by
    unfold ntLevels
    exact_mod_cast (by omega : Nat.log 2 (6 * U) + 1 ≤ Nat.log 2 U + 4)
  -- `log₂ U + 4 ≤ 2 log U + 8 log 2 ≤ 10 log u`
  linarith

/-- [VW13, Theorem 3.3] for programs of the light language: Negative Triangle from Exact Triangle,
with c = 6. -/
theorem claim_VW13_Theorem_3_3_sourceProof : Claim.VW13_Theorem_3_3 lightModel := by
  refine ⟨6, 4880, by norm_num, by norm_num, fun T hT hs =>
    isHost_nt.solvedIn hs fun Tn hTn n U u hn hU hu => ?_⟩
  have hτ : (Tn n (6 * U) : ℝ) ≤ T n (6 * u) :=
    hTn n (6 * U) (6 * u) hn (by omega) (by push_cast; linarith)
  have hg := hT.1 n (6 * u) hn
  have hl := logU_pos (6 * u)
  have hlu := logU_pos u
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hN : (n : ℝ) ^ 2 ≤ T n (6 * u) := by nlinarith
  have hL := ntLevels_le hU hu
  have hL1 : (1 : ℝ) ≤ ntLevels U := by
    unfold ntLevels
    exact_mod_cast Nat.le_add_left 1 _
  generalize T n (6 * u) = τ at *
  unfold ntTime
  push_cast
  generalize (ntLevels U : ℝ) = L at *
  generalize (Tn n (6 * U) : ℝ) = t at *
  have hτ0 : 0 ≤ τ := by linarith
  have hround : 154 * ((n : ℝ) * n) + 92 + 2 * t ≤ 248 * τ := by nlinarith
  calc 120 * ((n : ℝ) * n) + 120 + L * (154 * ((n : ℝ) * n) + 92 + 2 * t)
      ≤ 240 * τ + L * (248 * τ) := by
        have := mul_le_mul_of_nonneg_left hround (by linarith : (0 : ℝ) ≤ L)
        nlinarith
    _ ≤ 488 * (L * τ) := by nlinarith
    _ ≤ 488 * (10 * logU u * τ) := by
        have := mul_le_mul_of_nonneg_right hL hτ0
        linarith
    _ = 4880 * (τ * logU u) := by ring

end Light.Sec3

end
end


theorem solution : ThreeSumApsp.Claim.VW13_Theorem_3_3 Light.lightModel := by
  exact @Light.Sec3.claim_VW13_Theorem_3_3_sourceProof

#print axioms solution
