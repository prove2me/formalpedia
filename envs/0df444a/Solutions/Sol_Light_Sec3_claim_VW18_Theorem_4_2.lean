-- Prove2me | solution 1 for Light.Sec3.claim_VW18_Theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T09:40:25.213404+00:00
-- url     : https://prove2.me/submissions/21e80e5e-0968-4967-b5ec-555de0143302

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
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_AllPairs
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_BitSearch
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_FindNegativeTriangle
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
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
import Mathlib.Algebra.Order.Floor.Semifield
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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
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
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSumApsp_Spec_bitLo_step

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

/-- A loop whose test holds: one round, then the loop again. -/
theorem Ends.whileStep {σ c s T} {Q : State → Prop} (T₁ T₂ : ℕ) (hs : c.Safe lim σ) (hc : c.Holds σ)
    (h : Ends lim P d s σ T₁ fun σ' => Ends lim P d (.while c s) σ' T₂ Q)
    (hT : c.cost + 1 + T₁ + T₂ ≤ T) : Ends lim P d (.while c s) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .whileTrue hs hc he₁ he₂, by omega, hq⟩

/-- A loop whose test fails. -/
theorem Ends.whileDone {σ c s T} {Q : State → Prop} (hs : c.Safe lim σ) (hc : ¬ c.Holds σ)
    (hQ : Q σ) (hT : c.cost + 1 ≤ T) : Ends lim P d (.while c s) σ T Q :=
  ⟨σ, _, .whileFalse hs hc, hT, hQ⟩

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

/-- Loops whose number of rounds depends on the data.  I is the invariant, m a quantity that every
round decreases, and b bounds the cost of a round. -/
theorem Ends.whileVariant {σ c s T} {Q : State → Prop} (I : State → Prop) (m : State → ℕ) (b : ℕ)
    (hI : I σ) (hsafe : ∀ σ, I σ → c.Safe lim σ)
    (hs : ∀ σ, I σ → c.Holds σ → Ends lim P d s σ b fun σ' => I σ' ∧ m σ' < m σ)
    (hn : ∀ σ, I σ → ¬ c.Holds σ → Q σ) (hT : m σ * (c.cost + 1 + b) + (c.cost + 1) ≤ T) :
    Ends lim P d (.while c s) σ T Q := by
  have key : ∀ n σ, I σ → m σ ≤ n →
      Ends lim P d (.while c s) σ (m σ * (c.cost + 1 + b) + (c.cost + 1)) Q := by
    intro n
    induction n with
    | zero =>
      intro σ h hm
      by_cases hc : c.Holds σ
      · obtain ⟨σ₁, k₁, -, -, -, hlt⟩ := hs σ h hc
        omega
      · exact ⟨σ, _, .whileFalse (hsafe _ h) hc, by omega, hn σ h hc⟩
    | succ n ih =>
      intro σ h hm
      by_cases hc : c.Holds σ
      · obtain ⟨σ₁, k₁, he₁, hk₁, hI₁, hlt⟩ := hs σ h hc
        obtain ⟨σ₂, k₂, he₂, hk₂, hq⟩ := ih σ₁ hI₁ (by omega)
        refine ⟨σ₂, _, .whileTrue (hsafe _ h) hc he₁ he₂, ?_, hq⟩
        have h1 : (m σ₁ + 1) * (c.cost + 1 + b) ≤ m σ * (c.cost + 1 + b) :=
          Nat.mul_le_mul_right _ hlt
        have h2 : (m σ₁ + 1) * (c.cost + 1 + b) = m σ₁ * (c.cost + 1 + b) + (c.cost + 1 + b) := by
          ring
        omega
      · exact ⟨σ, _, .whileFalse (hsafe _ h) hc, by omega, hn σ h hc⟩
  exact (key _ σ hI le_rfl).mono hT fun _ h => h

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

/-- An assignment at the end of the program. -/
theorem Ends.setLast {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {Q : State → Prop}
    (h : Q ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩)
    (hs : e.Safe lim ⟨loc, μ⟩ := by (((try have := Light.Std.space_le (by assumption)));
                                           ((try have := Light.Std.const_le (by assumption)));
                                           (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : e.cost + 1 ≤ T := by first
                                                                                                                                   |
                                                                                                                                     ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
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
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set hs hT h

/-- An assignment, followed by the rest of the program. -/
theorem Ends.setThen {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩ (T - (e.cost + 1)) Q)
    (hs : e.Safe lim ⟨loc, μ⟩ := by (((try have := Light.Std.space_le (by assumption)));
                                           ((try have := Light.Std.const_le (by assumption)));
                                           (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : e.cost + 1 ≤ T := by first
                                                                                                                                   |
                                                                                                                                     ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
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
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.set hs le_rfl h) hT

















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

/-- Every index below `m * n` is the index of a pair. -/
theorem exists_eq_mul_add_of_lt_mul {t m n : ℕ} (h : t < m * n) : ∃ a < m, ∃ b < n, t = a * n + b :=
  ⟨t / n, div_lt_of_lt_mul' h, t % n, mod_lt_of_lt_mul h, (Nat.div_add_mod' t n).symm⟩










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




























/-- The entries of a list in which entry `q < l.length` was replaced by `a`. -/
theorem getD_set_of_lt {l : List α} {q : ℕ} (hq : q < l.length) (a d : α) (q' : ℕ) :
    (l.set q a).getD q' d = if q' = q then a else l.getD q' d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd h1.symm h2
  · exact absurd (h3 ▸ hq) (by omega)
  · rfl


















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

@[simp] theorem length_readSeg : (readSeg μ a n).length = n := by simp [readSeg]

@[simp] theorem getElem_readSeg {i : ℕ} (h : i < (readSeg μ a n).length) :
    (readSeg μ a n)[i] = μ (a + i) := by
  simp [readSeg]








/-- Reading a cell of a segment. -/
theorem Seg.get (h : Seg μ a l) {i : ℕ} (hi : i < l.length) : μ (a + i) = l[i] := h i hi





/-- A segment determines its list. -/
theorem Seg.eq_readSeg (h : Seg μ a l) : l = readSeg μ a l.length :=
  List.ext_getElem (by simp) fun i h₁ h₂ => by rw [getElem_readSeg, h i h₁]







































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_49031_0 apspMacro_49031_1);
                                                                                  (first
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_49031_2));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_49031_2 apspMacro_49031_0 (by omega)));
                                                                                                  (revert apspMacro_49031_2)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((simp [] at apspMacro_49031_1);
                                                                                        (((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_49031_3));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_49031_3 apspMacro_49031_0 (by omega)));
                                                                                                  (revert apspMacro_49031_3)));
                                                                                            (intros);
                                                                                            (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                        (omega))
                                                                                    |
                                                                                      ((((repeat
                                                                                                (((with_reducible
                                                                                                        rename Light.SameOn _ _ _ => apspMacro_49031_4));
                                                                                                  ((try
                                                                                                        have :=
                                                                                                          apspMacro_49031_4 apspMacro_49031_0 (by omega)));
                                                                                                  (revert apspMacro_49031_4)));
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














theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl

/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)






























































































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
    ⟨fun i hi => wrote_done (f := fun i => μ (src + i)) hi, by ((try refine Light.SameOn.cell ?_); (intro apspMacro_53739_0 apspMacro_53739_1);
                                                                    (first
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_53739_2));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_53739_2 apspMacro_53739_0 (by omega)));
                                                                                    (revert apspMacro_53739_2)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((simp [] at apspMacro_53739_1);
                                                                          (((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_53739_3));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_53739_3 apspMacro_53739_0 (by omega)));
                                                                                    (revert apspMacro_53739_3)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_53739_4));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_53739_4 apspMacro_53739_0 (by omega)));
                                                                                    (revert apspMacro_53739_4)));
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
    ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by ((try refine Light.SameOn.cell ?_); (intro apspMacro_54606_0 apspMacro_54606_1);
                                                                                   (first
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_54606_2));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_54606_2 apspMacro_54606_0 (by omega)));
                                                                                                   (revert apspMacro_54606_2)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((simp [] at apspMacro_54606_1);
                                                                                         (((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_54606_3));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_54606_3 apspMacro_54606_0 (by omega)));
                                                                                                   (revert apspMacro_54606_3)));
                                                                                             (intros);
                                                                                             (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                                         (omega))
                                                                                     |
                                                                                       ((((repeat
                                                                                                 (((with_reducible
                                                                                                         rename Light.SameOn _ _ _ => apspMacro_54606_4));
                                                                                                   ((try
                                                                                                         have :=
                                                                                                           apspMacro_54606_4 apspMacro_54606_0 (by omega)));
                                                                                                   (revert apspMacro_54606_4)));
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
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Logs







end Logs

open Logs

/-! ## The logarithm, rounded down -/















































/-! ## The logarithm, rounded up -/










































/-! ## The cube root, rounded up -/







theorem le_cbrtLeast_pow (n : ℕ) : n ≤ cbrtLeast n ^ 3 := Nat.find_spec (exists_le_cube n)

theorem pow_lt_of_lt_cbrtLeast {n s : ℕ} (h : s < cbrtLeast n) : s ^ 3 < n :=
  not_le.1 (Nat.find_min (exists_le_cube n) h)

theorem cbrtLeast_le {n s : ℕ} (h : n ≤ s ^ 3) : cbrtLeast n ≤ s :=
  Nat.find_min' (exists_le_cube n) h

theorem cbrtLeast_le_self (n : ℕ) : cbrtLeast n ≤ n :=
  cbrtLeast_le (Nat.le_self_pow (by norm_num) n)

/-- The number ⌈n^{1/3}⌉ is at least 1 for n ≥ 1. -/
theorem one_le_cbrtLeast {n : ℕ} (hn : 1 ≤ n) : 1 ≤ cbrtLeast n := by
  by_contra h
  have hpow := le_cbrtLeast_pow n
  rw [show cbrtLeast n = 0 by omega] at hpow
  omega

/-- The cube of the rounded cube root is at most 8 n. -/
theorem cbrtLeast_pow_le (n : ℕ) : cbrtLeast n ^ 3 ≤ 8 * n := by
  rcases Nat.eq_zero_or_pos (cbrtLeast n) with h | h
  · simp [h]
  obtain ⟨s, hs⟩ : ∃ s, cbrtLeast n = s + 1 := ⟨cbrtLeast n - 1, by omega⟩
  have h1 : s ^ 3 < n := pow_lt_of_lt_cbrtLeast (by omega)
  rw [hs]
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0
    omega
  · calc (s + 1) ^ 3 ≤ (2 * s) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * s ^ 3 := by ring
      _ ≤ 8 * n := by omega

/-- The squares and cubes of the candidates fit in a word. -/
private theorem abs_cube_le {n i : ℕ} (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word)
    (hi : i ≤ cbrtLeast n) : |(i : ℤ) * i| ≤ lim.word ∧ |(i : ℤ) * i * i| ≤ lim.word := by
  have hcube : i * i * i ≤ 8 * n :=
    calc i * i * i = i ^ 3 := by ring
      _ ≤ cbrtLeast n ^ 3 := Nat.pow_le_pow_left hi 3
      _ ≤ 8 * n := cbrtLeast_pow_le n
  have hsquare : i * i ≤ i * i * i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp
    · exact Nat.le_mul_of_pos_right _ h
  have hcube' : (i : ℤ) * i * i ≤ 8 * n := by exact_mod_cast hcube
  have hsquare' : (i : ℤ) * i ≤ 8 * n := by exact_mod_cast hsquare.trans hcube
  have h2 : (0 : ℤ) ≤ (i : ℤ) * i := by positivity
  have h3 : (0 : ℤ) ≤ (i : ℤ) * i * i := by positivity
  push_cast at hword
  exact ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩











/-- **cbrtCeil(n)** returns the least s with s³ ≥ n and leaves the memory as it is. -/
theorem cbrtCeil_meets {p n : ℕ} (hp : P[p]? = some cbrtCeilBody) (μ : ℕ → ℤ)
    (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [n] μ (cbrtCeilTime n) fun r μ' => r = (cbrtLeast n : ℤ) ∧ μ' = μ := by
  have hsn : cbrtLeast n ≤ n := cbrtLeast_le_self n
  refine .of_body hp ?_
  unfold cbrtCeilBody cbrtCeilTime
  -- s := 0
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
            -- while s³ < n.  Before round i, s = i.
            
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
  -- while s³ < n.  Before round i, s = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [n, i], μ⟩) (cbrtLeast n) (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt : (i : ℤ) * i * i < n := by
      have := pow_lt_of_lt_cbrtLeast hi
      rw [show i ^ 3 = i * i * i by ring] at this
      exact_mod_cast this
    -- The test is safe and holds.  s := s + 1 is safe and leads to the next state.
    exact ⟨by simpa using abs_cube_le hword hi.le, by simpa using hlt, by (((try have := Light.Std.space_le (by assumption)));
                                                                              ((try have := Light.Std.const_le (by assumption)));
                                                                              (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hle : (n : ℤ) ≤ (cbrtLeast n : ℤ) * cbrtLeast n * cbrtLeast n := by
      have := le_cbrtLeast_pow n
      rw [show cbrtLeast n ^ 3 = cbrtLeast n * cbrtLeast n * cbrtLeast n by ring] at this
      exact_mod_cast this
    refine ⟨by simpa using abs_cube_le hword le_rfl, by simpa using hle, ?_⟩
    -- the result is s
    focus
      ((((first
              | refine Light.Ends.seqSelf ?_
              | refine Light.Ends.skipLast ?_));
          (repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)));
      (refine Light.Ends.setToThen (cbrtLeast n) ?_ ?_ ?_);
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

/-! ## Halves, rounded up -/

































end Light

end
end

section


/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light

open ThreeSumApsp.WordRam







































/-- The bound grows with its first parameter. -/
theorem polyBound_cons_le {p p' : ℕ} (h : p ≤ p') (s k : ℕ) (params : List ℕ) :
    polyBound s k (p :: params) ≤ polyBound s k (p' :: params) := by
  simp only [polyBound, List.map_cons, List.prod_cons]
  gcongr










































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

/-- A bound with an explicit nonnegative constant. -/
theorem of_le_const_mul {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ x, dom x → f x ≤ C * g x) :
    Dominated dom f g :=
  ⟨C, hC, hfg⟩

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

/-- A nonnegative constant factor on the left side is absorbed. -/
theorem const_mul (hfg : Dominated dom f g) {c : ℝ} (hc : 0 ≤ c) :
    Dominated dom (fun x => c * f x) g := by
  obtain ⟨C, hC, hf⟩ := hfg
  refine ⟨c * C, mul_nonneg hc hC, fun x hx => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x hx) hc






























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





/-- `log 4 = 2 log 2`. -/
theorem log_four : log 4 = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]


































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

theorem mon_single [DecidableEq ι] (i : ι) (x : α) : s.mon (Pi.single i 1) x = s.base i x := by
  simp [mon, Pi.single_apply, pow_ite]

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

/-- A count that is at most a constant times a base. -/
theorem of_dominated_base [DecidableEq ι] (i : ι)
    (h : Dominated s.dom (fun x => (t x : ℝ)) (s.base i)) : s.SoftO t (Pi.single i 1) :=
  ⟨0, h.congr (fun _ _ => rfl) fun x _ => by rw [pow_zero, mon_single, one_mul]⟩

/-- A count that is at most a base. -/
theorem of_le_base [DecidableEq ι] (i : ι) (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.base i x) :
    s.SoftO t (Pi.single i 1) :=
  of_dominated_base i (.of_le h)





/-- The bound, written out. -/
theorem exists_le (h : s.SoftO t e) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ x, s.dom x → (t x : ℝ) ≤ C * (s.hidden x ^ c * s.mon e x) :=
  let ⟨c, C, hC, hle⟩ := h
  ⟨C, c, hC, hle⟩

/-- If `hidden = 1`, the bound is the monomial. -/
theorem dominated (h : s.SoftO t e) (hhidden : ∀ x, s.dom x → s.hidden x = 1) :
    Dominated s.dom (fun x => (t x : ℝ)) (s.mon e) :=
  let ⟨_, h⟩ := h
  h.congr (fun _ _ => rfl) fun x hx => by rw [hhidden x hx, one_pow, one_mul]

/-! ### The rules -/

/-- The exponents may be raised. -/
theorem mono (h : s.SoftO t e) (he : ∀ i, e i ≤ e' i) : s.SoftO t e' :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_right fun _ hx => pow_mul_mon_le le_rfl he hx⟩

/-- A smaller count has the same bound. -/
theorem of_le (h : s.SoftO t₂ e) (hle : ∀ x, s.dom x → t₁ x ≤ t₂ x) : s.SoftO t₁ e :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_left fun x hx => Nat.cast_le.2 (hle x hx)⟩

/-- A quantity `f` that is at most `g` everywhere has the bound of `g`, at any argument. -/
theorem of_forall_le {β : Type*} {f g : β → ℕ} (hle : ∀ y, f y ≤ g y) {u : α → β}
    (h : s.SoftO (fun x => g (u x)) e) : s.SoftO (fun x => f (u x)) e :=
  h.of_le fun _ _ => hle _






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




/-- A bound on the numbers of the list is a bound on the entries of the matrix. -/
theorem abs_entry_le (n : ℕ) {L : List ℤ} {U : ℤ} (hU : 0 ≤ U) (hL : AbsLe L U) (i j : ℕ) :
    |entry n L i j| ≤ U :=
  AbsLe.abs_getD_le hU hL _

























/-! ## Operations on matrices -/













/-- A block has `h²` entries. -/
@[simp] theorem length_subMat (s h r0 c0 : ℕ) (L : List ℤ) :
    (subMat s h r0 c0 L).length = h * h := by
  simp [subMat]

/-- The entry `(i, j)` of a block is the entry `(r0 + i, c0 + j)` of the matrix. -/
theorem entry_subMat {s h r0 c0 : ℕ} {L : List ℤ} {i j : ℕ} (hi : i < h) (hj : j < h) :
    entry h (subMat s h r0 c0 L) i j = entry s L (r0 + i) (c0 + j) := by
  rw [entry, subMat, List.getD_map_range _ (Nat.mul_add_lt_mul hi hj), Nat.mul_add_div_of_lt hj,
    Nat.mul_add_mod_of_lt hj]

/-- A bound on the entries of a matrix is a bound on the entries of its blocks. -/
theorem abs_le_of_mem_subMat {s h r0 c0 : ℕ} {L : List ℤ} {U : ℤ} (hU : 0 ≤ U) (hL : AbsLe L U) :
    AbsLe (subMat s h r0 c0 L) U :=
  List.forall_mem_map.2 fun _ _ => AbsLe.abs_getD_le hU hL _

/-! ## The (min,+)-product -/



























/-- The entries of the product of two matrices with entries of absolute value at most `U` have
absolute value at most `2U`. -/
theorem abs_minPlusEntry_le {n : ℕ} (hn : 1 ≤ n) {A B : List ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hA : AbsLe A U) (hB : AbsLe B U) (i j : ℕ) : |minPlusEntry n A B i j| ≤ 2 * U := by
  obtain ⟨k, -, he⟩ := exists_minPlusEntry_eq hn A B i j
  have ha := AbsLe.abs_getD_le hU hA (i * n + k)
  have hb := AbsLe.abs_getD_le hU hB (k * n + j)
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)








end ThreeSumApsp.Spec

end
end

section


/-!
# Copying a block of a matrix

A routine for the hosts of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).
subCopy(s, h, src, r0, c0, dst) copies the h × h block with upper left corner (r0,
c0) of the s × s matrix at src (row major) to dst (row major), one row at a time, with the routine
copy.  The destination lies behind the matrix.

The specification is subCopy_meets: afterwards the list subMat s h r0 c0 L stands at dst, and no
other cell has changed.  The proof is a loop over the rows with the invariant SubCopy.Inv; that
row i of the block is a piece of row r0 + i of the matrix is SubCopy.row_eq.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace SubCopy












end SubCopy












/-! ## The specification -/

namespace SubCopy

/-- Row i of the block is a piece of row r0 + i of the matrix. -/
theorem row_eq {μ : ℕ → ℤ} {s h src r0 c0 i j : ℕ} {L : List ℤ} (hL : Seg μ src L)
    (hlen : L.length = s * s) (hr : r0 + h ≤ s) (hc : c0 + h ≤ s) (hi : i < h) (hj : j < h) :
    μ (src + ((r0 + i) * s + c0) + j) = entry h (subMat s h r0 c0 L) i j := by
  have hidx : (r0 + i) * s + (c0 + j) < L.length :=
    hlen ▸ Nat.mul_add_lt_mul (by omega : r0 + i < s) (by omega : c0 + j < s)
  rw [entry_subMat hi hj, entry, List.getD_eq_getElem _ _ hidx, ← hL _ hidx]
  congr 1
  omega







end SubCopy

open SubCopy in
/-- **subCopy** writes the block of the matrix L at src to dst and changes nothing else.  The block
lies within the matrix and the destination behind it (hplace); the destination lies within the
memory, and one more level of calls is allowed (hlim). -/
theorem subCopy_meets {pSub pCopy : ℕ} (hSub : P[pSub]? = some (subCopyBody pCopy))
    (hCopy : P[pCopy]? = some copyBody) {μ : ℕ → ℤ} {s src : ℕ} {L : List ℤ} (h r0 c0 dst : ℕ)
    (hL : Seg μ src L) (hlen : L.length = s * s)
    (hplace : r0 + h ≤ s ∧ c0 + h ≤ s ∧ src + s * s ≤ dst)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ dst + h * h ≤ lim.space ∧ d < lim.depth) :
    Meets lim P pSub d [(s : ℤ), h, src, r0, c0, dst] μ (subCopyTime h) fun _ μ' =>
      Seg μ' dst (subMat s h r0 c0 L) ∧ SameOutside μ μ' dst (h * h) := by
  obtain ⟨hr, hc, hsrc⟩ := hplace
  obtain ⟨hw, hdst, hd⟩ := hlim
  have hh : h ≤ h * h := Nat.le_mul_self h
  unfold subCopyTime
  -- for i < h
  refine .of_body hSub (Ends.for (Inv μ s h src r0 c0 dst (subMat s h r0 c0 L)) h (16 * h + 23)
    ?start ?round ?done ?bound)
  case start =>
    exact ⟨0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl,
      fun q hq => absurd hq (by omega), .refl⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hrows, hrest⟩
    -- Row r0 + i of the matrix and row i of the block lie within their arrays.
    have hrowS : (r0 + i) * s + s ≤ s * s := Nat.mul_add_le_mul (by omega) le_rfl
    have hrowZ : 0 ≤ ((r0 : ℤ) + i) * s ∧ ((r0 : ℤ) + i) * s + s ≤ s * s := by
      exact_mod_cast And.intro (Nat.zero_le _) hrowS
    have hrowD : i * h + h ≤ h * h := Nat.mul_add_le_mul hi le_rfl
    -- copy(src + (r0 + i) s + c0, dst + i h, h)
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
              ((copy_meets hCopy (src := src + ((r0 + i) * s + c0)) (dst :=
                  dst + i * h) (n := h) hw (by omega) (by omega) (.inl (by omega)))
                _ (by omega))
              ?_ ?_ ?_ ?_
        |
          refine
            Light.Ends.callToThen
              (copy_meets hCopy (src := src + ((r0 + i) * s + c0)) (dst :=
                dst + i * h) (n := h) hw (by omega) (by omega) (.inl (by omega)))
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
          ((rintro r' μ'' ⟨hcopy, hout⟩);
            (try with_unfolding_none refine Light.Ends.skip ?_)))
    refine ⟨by simp, r', μ'', by rw [update_frame_setLocal]; rfl, fun q hq => ?_,
      hrest.trans (hout.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge q (i * h) with hq' | hq'
    · -- The earlier rows lie below dst + i h and have not been touched.
      exact (hout _ (.inl (by omega))).trans (hrows q hq')
    · -- Row i has just been copied from the matrix, which is as at the start.
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hq'
      have hj : j < h := by rw [Nat.add_mul, Nat.one_mul] at hq; omega
      rw [← Nat.add_assoc, hcopy j hj, hrest _ (.inl (by omega)), row_eq hL hlen hr hc hi hj]
  case done =>
    rintro _ - ⟨r, μ', rfl, hrows, hrest⟩
    exact ⟨fun q hq => (hrows q (by simpa using hq)).trans (List.getD_eq_getElem _ _ hq), hrest⟩

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

/-- An answer is 0 or 1. -/
theorem flag_mem (p : Prop) : 0 ≤ flag p ∧ flag p < 2 := by
  by_cases h : p
  · simp [flag_of h]
  · simp [flag_of_not h]

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
    (hs : Kept μ μ' fr := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_94222_0 apspMacro_94222_1);
                                 (first
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_94222_2));
                                                 ((try
                                                       have :=
                                                         apspMacro_94222_2 apspMacro_94222_0 (by omega)));
                                                 (revert apspMacro_94222_2)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((simp [] at apspMacro_94222_1);
                                       (((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_94222_3));
                                                 ((try
                                                       have :=
                                                         apspMacro_94222_3 apspMacro_94222_0 (by omega)));
                                                 (revert apspMacro_94222_3)));
                                           (intros);
                                           (try simp only [Function.update_apply, Light.wrote] at *)));
                                       (omega))
                                   |
                                     ((((repeat
                                               (((with_reducible
                                                       rename Light.SameOn _ _ _ => apspMacro_94222_4));
                                                 ((try
                                                       have :=
                                                         apspMacro_94222_4 apspMacro_94222_0 (by omega)));
                                                 (revert apspMacro_94222_4)));
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
# The two tasks between Negative Triangle and the (min,+)-product

[VW18, Theorem 4.2], one of the reductions behind Theorem 21(b), goes from
deciding Negative Triangle to the (min,+)-product in three steps: finding a negative triangle
([VW18, Lemma 4.1]), finding for all pairs `(i, j)` at once whether some `k` has `X[i,k] + Y[k,j] <
V[i,j]`, and a search for all entries of the product at once.  Each step is a host over an arbitrary
solver of the task below it (isHost_find, isHost_pairs, isHost_mp).  This file fixes the two tasks
in the middle, findTask and pairsTask.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec











































































/-- An instance stays where it is if no cell below the free pointer changes, except the flags. -/
theorem PairsInst.Pre.keep {q : PairsInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : q.Pre μ fr)
    (hs : KeptBut μ μ' fr q.out (q.n * q.n) := by ((try refine Light.SameOn.cell ?_); (intro apspMacro_95863_0 apspMacro_95863_1);
                                                      (first
                                                        |
                                                          ((((repeat
                                                                    (((with_reducible
                                                                            rename Light.SameOn _ _ _ => apspMacro_95863_2));
                                                                      ((try
                                                                            have :=
                                                                              apspMacro_95863_2 apspMacro_95863_0 (by omega)));
                                                                      (revert apspMacro_95863_2)));
                                                                (intros);
                                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                                            (omega))
                                                        |
                                                          ((simp [] at apspMacro_95863_1);
                                                            (((repeat
                                                                    (((with_reducible
                                                                            rename Light.SameOn _ _ _ => apspMacro_95863_3));
                                                                      ((try
                                                                            have :=
                                                                              apspMacro_95863_3 apspMacro_95863_0 (by omega)));
                                                                      (revert apspMacro_95863_3)));
                                                                (intros);
                                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                                            (omega))
                                                        |
                                                          ((((repeat
                                                                    (((with_reducible
                                                                            rename Light.SameOn _ _ _ => apspMacro_95863_4));
                                                                      ((try
                                                                            have :=
                                                                              apspMacro_95863_4 apspMacro_95863_0 (by omega)));
                                                                      (revert apspMacro_95863_4)));
                                                                (intros);
                                                                (try simp only [Function.update_apply, Light.wrote] at *)));
                                                            (fail
                                                                "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                          its condition K x does not follow from the hypotheses."))))) : q.Pre μ' fr := by
  (obtain ⟨⟩ := id h)
  exact { h with segX := h.segX.keep, segY := h.segY.keep, segV := h.segV.keep }
















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

/-- `a ⌈/⌉ b` pieces of size `b` cover `a`. -/
theorem le_ceilDiv_mul {a b : ℕ} (hb : 0 < b) : a ≤ a ⌈/⌉ b * b :=
  (ceilDiv_le_iff hb).1 le_rfl

/-- `a ⌈/⌉ b` pieces of size `b` overshoot `a` by less than one piece. -/
theorem ceilDiv_mul_lt {a b : ℕ} (hb : 0 < b) : a ⌈/⌉ b * b < a + b := by
  have := Nat.div_mul_le_self (a + b - 1) b
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega











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
# All pairs with a witness, by marking

The middle step of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).
Given three `n × n` matrices `X`, `Y`, `V`, the task is to mark all pairs `(i, j)` for which some
`k` has `X[i,k] + Y[k,j] < V[i,j]` (`Witness`, `PairHit`).  The three ranges are cut into blocks of
`s` indices.

* The last block of a range is moved back so that it ends at `n`; blocks may overlap, and there are
  no padding vertices (`blockOff`, `blockCount`, `exists_block`).
* For a triple of blocks, the `s × s × s` instance `blockTri` has the weights `X[i,k]`, `Y[k,j]` and
  `-V[i,j]`; a pair that is already marked gets the weight `F = 2U + 1` instead of `-V[i,j]`
  (`maskNeg`), which is too large for a negative triangle.
* So every negative triangle that is found is an unmarked pair with a witness (`unmarked_of_neg`),
  marking it keeps the marks right (`Marks.set`) and lowers the number of unmarked pairs
  (`count_set_one`).  If the instance of a triple has no negative triangle, then every pair of the
  triple with a witness in the middle block is marked (`BlockDone`, `blockDone_of_not`), and this
  stays so when more pairs are marked (`BlockDone.set`).
* When all triples are done, the marks are the answer (`Marks.complete`).
* `tripleIdx p I K J` is the position of a triple in the order in which the triples are visited.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Blocks -/







/-- A block ends at `n` or before. -/
theorem blockOff_add_le {n s : ℕ} (hs : s ≤ n) (I : ℕ) : blockOff n s I + s ≤ n := by
  unfold blockOff
  split_ifs <;> omega

/-- `i` blocks do not cover the range exactly if `i` is less than the number of blocks. -/
theorem lt_blockCount_iff {n s : ℕ} (hs : 1 ≤ s) (i : ℕ) : i < blockCount n s ↔ i * s < n :=
  Nat.lt_ceilDiv_iff hs

/-- The blocks overshoot the range by less than one block. -/
theorem blockCount_mul_lt {n s : ℕ} (hs : 1 ≤ s) : blockCount n s * s < n + s :=
  Nat.ceilDiv_mul_lt hs

/-- The blocks cover the range. -/
theorem le_blockCount_mul {n s : ℕ} (hs : 1 ≤ s) : n ≤ blockCount n s * s :=
  Nat.le_ceilDiv_mul hs

/-- A range that is not empty has a block. -/
theorem blockCount_pos {n s : ℕ} (hs : 1 ≤ s) (hn : 1 ≤ n) : 1 ≤ blockCount n s :=
  (lt_blockCount_iff hs 0).2 (by omega)

/-- There are at most `n` blocks. -/
theorem blockCount_le {n s : ℕ} (hs : 1 ≤ s) : blockCount n s ≤ n :=
  (Nat.ceilDiv_le_iff hs).2 (Nat.le_mul_of_pos_right n hs)

/-- Every index lies in a block. -/
theorem exists_block {n s i : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ n) (hi : i < n) :
    ∃ I < blockCount n s, ∃ a < s, i = blockOff n s I + a := by
  have hdiv : i / s * s + i % s = i := Nat.div_add_mod' i s
  have hmod : i % s < s := Nat.mod_lt _ hs1
  refine ⟨i / s, (lt_blockCount_iff hs1 _).2 (by omega), ?_⟩
  unfold blockOff
  split_ifs with h
  · exact ⟨i % s, hmod, hdiv.symm⟩
  · exact ⟨i - (n - s), by omega, by omega⟩

/-! ## The order of the triples -/




/-- The position determines the triple. -/
theorem tripleIdx_inj {p I K J I' K' J' : ℕ} (hK : K < p) (hJ : J < p) (hK' : K' < p)
    (hJ' : J' < p) (h : tripleIdx p I K J = tripleIdx p I' K' J') : I = I' ∧ K = K' ∧ J = J' := by
  obtain ⟨hIK, hJJ⟩ := Nat.mul_add_inj_of_lt hJ hJ' h
  obtain ⟨hII, hKK⟩ := Nat.mul_add_inj_of_lt hK hK' hIK
  exact ⟨hII, hKK, hJJ⟩

/-- The positions are below `p³`. -/
theorem tripleIdx_lt {p I K J : ℕ} (hI : I < p) (hK : K < p) (hJ : J < p) :
    tripleIdx p I K J < p * p * p :=
  Nat.mul_add_lt_mul (Nat.mul_add_lt_mul hI hK) hJ

/-- The next triple, when only `J` moves. -/
theorem tripleIdx_succ_J (p I K J : ℕ) : tripleIdx p I K (J + 1) = tripleIdx p I K J + 1 := rfl

/-- The next triple, when `J` starts again and `K` moves. -/
theorem tripleIdx_succ_K (p I K : ℕ) :
    tripleIdx (p + 1) I (K + 1) 0 = tripleIdx (p + 1) I K p + 1 := by
  unfold tripleIdx
  ring

/-- The next triple, when `J` and `K` start again and `I` moves. -/
theorem tripleIdx_succ_I (p I : ℕ) :
    tripleIdx (p + 1) (I + 1) 0 0 = tripleIdx (p + 1) I p p + 1 := by
  unfold tripleIdx
  ring

/-- The position after the last triple. -/
theorem tripleIdx_top (p : ℕ) : tripleIdx p p 0 0 = p * p * p := by
  simp [tripleIdx]

/-! ## The third matrix of a block instance -/




/-- The third matrix is as long as the shorter of the two lists. -/
@[simp] theorem length_maskNeg (F : ℤ) (O V : List ℤ) :
    (maskNeg F O V).length = min O.length V.length := by
  simp [maskNeg]

/-- An entry of the third matrix. -/
theorem getElem_maskNeg {F : ℤ} {O V : List ℤ} {i : ℕ} (hO : i < O.length) (hV : i < V.length)
    (h : i < (maskNeg F O V).length) : (maskNeg F O V)[i] = if O[i] = 1 then F else -V[i] := by
  simp [maskNeg]

/-- An entry of the third matrix, read with a default. -/
theorem getD_maskNeg {F : ℤ} {O V : List ℤ} {i : ℕ} (hO : i < O.length) (hV : i < V.length) :
    (maskNeg F O V).getD i 0 = if O.getD i 0 = 1 then F else -V.getD i 0 := by
  have h : i < (maskNeg F O V).length := by
    rw [length_maskNeg]
    omega
  rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ hO, List.getD_eq_getElem _ _ hV,
    getElem_maskNeg hO hV]

/-- A bound on `F` and on the entries of `V` is a bound on the entries of the third matrix. -/
theorem abs_le_of_mem_maskNeg {F U : ℤ} {O V : List ℤ} (hF : |F| ≤ U) (hV : AbsLe V U) :
    AbsLe (maskNeg F O V) U := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < O.length ∧ i < V.length := by simpa using hi
  rw [getElem_maskNeg hi'.1 hi'.2]
  split_ifs
  · exact hF
  · rw [abs_neg]
    exact hV _ (List.getElem_mem _)

/-! ## Marks -/

























/-- The weight of a triangle of the instance for a triple of blocks. -/
theorem blockTri_S (n s : ℕ) (F : ℤ) (X Y V O : List ℤ) (oI oK oJ : ℕ) (a b c : Fin s) :
    (blockTri n s F X Y V O oI oK oJ).S a b c =
      entry n X (oI + a) (oK + b) + entry n Y (oK + b) (oJ + c) +
        if entry n O (oI + a) (oJ + c) = 1 then F else -entry n V (oI + a) (oJ + c) := by
  have h : a.val * s + c.val < s * s := Nat.mul_add_lt_mul a.2 c.2
  simp only [blockTri, TriangleInstance.S, triOf, entry_subMat a.2 b.2, entry_subMat b.2 c.2,
    getD_maskNeg (O := subMat n s oI oJ O) (V := subMat n s oI oJ V) (by simpa using h)
      (by simpa using h), entry_subMat a.2 c.2]

/-- If the instance of a triple of blocks has no negative triangle, then the triple is done. -/
theorem blockDone_of_not {n s : ℕ} {F : ℤ} {X Y V O : List ℤ} {oI oK oJ : ℕ}
    (h : ¬ (blockTri n s F X Y V O oI oK oJ).HasNegativeTriangle) :
    BlockDone n s X Y V O oI oK oJ := by
  intro a ha b hb c hc hlt
  by_contra hO
  refine h ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ?_⟩
  rw [blockTri_S, if_neg hO]
  exact Int.sub_neg_of_lt hlt

/-- A negative triangle of the instance of a triple of blocks is an unmarked pair with a
witness. -/
theorem unmarked_of_neg {n s : ℕ} {U : ℕ} {X Y V O : List ℤ} {oI oK oJ : ℕ}
    (hX : AbsLe X U) (hY : AbsLe Y U) {a b c : Fin s}
    (h : (blockTri n s (2 * U + 1) X Y V O oI oK oJ).S a b c < 0) :
    entry n O (oI + a) (oJ + c) ≠ 1 ∧ Witness n X Y V (oI + a) (oK + b) (oJ + c) := by
  have hx := abs_le.1 (abs_entry_le n (Int.natCast_nonneg U) hX (oI + a) (oK + b))
  have hy := abs_le.1 (abs_entry_le n (Int.natCast_nonneg U) hY (oK + b) (oJ + c))
  rw [blockTri_S] at h
  split_ifs at h with hO
  · -- a marked pair: `X + Y ≥ -2U` and `F = 2U + 1`, so the weight would be positive
    omega
  · -- an unmarked pair: the weight is `X + Y - V < 0`
    exact ⟨hO, by unfold Witness; omega⟩

/-- Marking a pair that has a witness keeps the marks right. -/
theorem Marks.set {n : ℕ} {X Y V O : List ℤ} (h : Marks n X Y V O) {i j : ℕ} (hi : i < n)
    (hj : j < n) (hit : PairHit n X Y V i j) : Marks n X Y V (O.set (i * n + j) 1) := by
  refine ⟨by simp [h.len], fun i' hi' j' hj' => ?_⟩
  rw [entry, List.getD_set_of_lt (h.len ▸ Nat.mul_add_lt_mul hi hj)]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := Nat.mul_add_inj_of_lt hj' hj e
    exact Or.inr ⟨rfl, hit⟩
  · exact h.sound i' hi' j' hj'

/-- Marking an unmarked pair makes the number of unmarked pairs smaller. -/
theorem count_set_one {O : List ℤ} {q : ℕ} (hq : q < O.length) (h0 : O.getD q 0 = 0) :
    (O.set q 1).count 0 + 1 = O.count 0 := by
  rw [List.getD_eq_getElem _ _ hq] at h0
  have hpos : 0 < O.count 0 := List.count_pos_iff.2 (h0 ▸ List.getElem_mem hq)
  rw [List.count_set hq, h0, if_pos (by decide), if_neg (by decide)]
  omega

/-- A triple of blocks that is done stays so when another pair is marked. -/
theorem BlockDone.set {n s : ℕ} {X Y V O : List ℤ} {oI oK oJ : ℕ}
    (h : BlockDone n s X Y V O oI oK oJ) {q : ℕ} (hq : q < O.length) :
    BlockDone n s X Y V (O.set q 1) oI oK oJ := by
  intro a ha b hb c hc hlt
  rw [entry, List.getD_set_of_lt hq]
  split_ifs
  · rfl
  · exact h a ha b hb c hc hlt

/-- **When all triples of blocks are done, the marks are the answer.** -/
theorem Marks.complete {n s : ℕ} {X Y V O : List ℤ} (h : Marks n X Y V O) (hs1 : 1 ≤ s)
    (hs : s ≤ n)
    (hdone : ∀ I < blockCount n s, ∀ K < blockCount n s, ∀ J < blockCount n s,
      BlockDone n s X Y V O (blockOff n s I) (blockOff n s K) (blockOff n s J))
    {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n O i j = flag (PairHit n X Y V i j) := by
  by_cases hit : PairHit n X Y V i j
  · rw [flag_of hit]
    obtain ⟨k, hk, hlt⟩ := hit
    obtain ⟨I, hI, a, ha, rfl⟩ := exists_block hs1 hs hi
    obtain ⟨K, hK, b, hb, rfl⟩ := exists_block hs1 hs hk
    obtain ⟨J, hJ, c, hc, rfl⟩ := exists_block hs1 hs hj
    exact hdone I hI K hK J hJ a ha b hb c hc hlt
  · rw [flag_of_not hit]
    exact (h.sound i hi j hj).resolve_right fun hmark => hit hmark.2

/-- At the beginning no pair is marked. -/
theorem marks_replicate (n : ℕ) (X Y V : List ℤ) : Marks n X Y V (List.replicate (n * n) 0) :=
  ⟨List.length_replicate, fun _ _ _ _ => Or.inl (by simp)⟩

end ThreeSumApsp.Spec

end
end

section


/-!
# All pairs with a witness, with an algorithm that finds a negative triangle

The middle step of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).  Given three n ×
n matrices X, Y, V, the host marks all pairs (i, j) for which some k has X[i,k] + Y[k,j] < V[i,j].
It cuts the three ranges into p = ⌈n/s⌉ blocks of s = ⌈n^{1/3}⌉ indices and visits the p³ triples of
blocks.  In each round it forms the s × s × s instance of the current triple, with the weights
X[i,k], Y[k,j], and -V[i,j], or 2U + 1 if (i, j) is already marked, and asks the solver for a
negative triangle.  A triangle that comes back marks a new pair; if there is none, the host goes on
to the next triple. So there are at most p³ + n² rounds.  The last block of a range is moved back so
that it ends at n (blocks may overlap), so there are no padding vertices.

The result is isHost_pairs : IsHost findTask pairsTask pairsTime pairsNeed.  The proof goes from the
inside to the outside: the third matrix of an instance (mask_meets); one question (ask_meets, with
the instance askInst and the meaning AskPost of the answer); the parts of a round (off_spec,
mark_spec, advance_spec); what a round achieves (Progress.mark and Progress.next: less is left to
do); a round (round_spec, with the invariant PairsInv); the host (pairs_spec; when nothing is left
to do the marks are the answer, Progress.complete).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedures -/

namespace Mask









end Mask









namespace Ask

















end Ask



















namespace Pairs























end Pairs

















































/-! ## Time and need -/



































namespace Pairs

variable {P₀ R : Program} {p₀ pCbrt pFill pAsk pSub pCopy pMask : ℕ} {T : ℕ → ℕ → ℕ}
  {r : ℕ → ℕ → Need}













/-! ## The third matrix of an instance -/

/-- **mask** turns the block A of V held at ac into the third matrix of the instance, with the block
O of marks held at tmp, and changes nothing else. -/
theorem mask_meets {P : Program} {pMask : ℕ} (hp : P[pMask]? = some maskBody) {μ : ℕ → ℤ}
    {ac tmp U : ℕ} (len : ℕ) (F : ℤ) {A O : List ℤ} (hA : Seg μ ac A) (hO : Seg μ tmp O)
    (hlen : A.length = len ∧ O.length = len) (hle : AbsLe A U)
    (hplace : ac + len ≤ tmp ∧ tmp + len ≤ lim.space)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ (U : ℤ) ≤ lim.word) :
    Meets lim P pMask d [(len : ℤ), F, ac, tmp] μ (maskTime len) fun _ μ' =>
      Seg μ' ac (maskNeg F O A) ∧ SameOutside μ μ' ac len := by
  obtain ⟨lA, lO⟩ := hlen
  obtain ⟨hw, hU⟩ := hlim
  unfold maskTime
  set f : ℕ → ℤ := fun i => (maskNeg F O A).getD i 0 with hf
  -- for q < len: before round q, the first q entries of the new matrix have been written
  refine .of_body hp (Ends.forFrame (fun q μ' => μ' = wrote μ ac f q) len wrote_zero.symm
    ?round ?done (hT := by simp; omega))
  case round =>
    rintro q _ hq rfl
    -- The two cells that the round reads are as at the start.
    have hmark : wrote μ ac f q (tmp + q) = O[q] := hO.keep.get (by omega)
    have hval : wrote μ ac f q (ac + q) = A[q] := (wrote_rest (by omega)).trans (hA q (by omega))
    have hfits := abs_le.1 ((hle.getElem (i := q) (by omega)).trans hU)
    have hfq : f q = if O[q] = 1 then F else -A[q] := by
      rw [hf]
      simp only [getD_maskNeg (F := F) (show q < O.length by omega) (show q < A.length by omega),
        List.getD_eq_getElem _ _ (show q < O.length by omega),
        List.getD_eq_getElem _ _ (show q < A.length by omega)]
    -- if tmp[q] = 1
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by simp [Limits.Addr, abs_le]; omega)
    · -- ac[q] := F
      refine Ends.storeTo (ac + q) F ⟨rfl, ?_⟩
      rw [← wrote_succ, hfq, if_pos (by simpa [hmark] using hc)]
    · -- ac[q] := 0 - ac[q]
      refine Ends.storeTo (ac + q) (-A[q]) ⟨rfl, ?_⟩ (by simp [Limits.Addr, abs_le, hval]; omega)
      rw [← wrote_succ, hfq, if_neg (by simpa [hmark] using hc)]
  case done =>
    rintro _ rfl
    dsimp only
    exact ⟨fun i hi => (wrote_done (by simpa [lA, lO] using hi)).trans
      (List.getD_eq_getElem _ _ hi), sameOutside_wrote le_rfl⟩

/-! ## One question -/















/-- It is an instance, once its three matrices stand at their places. -/
theorem askInst_pre {q : PairsInst} {O : List ℤ} {μ μ' : ℕ → ℤ} {fr s oI oK oJ : ℕ}
    (hpre : q.Pre μ fr) (hs : 1 ≤ s) (sAB : Seg μ' fr (askInst q O fr s oI oK oJ).AB)
    (sBC : Seg μ' (fr + s * s) (askInst q O fr s oI oK oJ).BC)
    (sAC : Seg μ' (fr + s * s + s * s) (askInst q O fr s oI oK oJ).AC) :
    (askInst q O fr s oI oK oJ).Pre μ' (fr + 3 * (s * s) + 3) :=
  have hU : (0 : ℤ) ≤ ((2 * q.U + 1 : ℕ) : ℤ) := by positivity
  have hF : |2 * (q.U : ℤ) + 1| ≤ ((2 * q.U + 1 : ℕ) : ℤ) := abs_le.2 ⟨by omega, by omega⟩
  have hle : ∀ L : List ℤ, AbsLe L q.U → ∀ z ∈ L, |z| ≤ ((2 * q.U + 1 : ℕ) : ℤ) := fun L hL z hz =>
    (hL z hz).trans (by push_cast; omega)
  { n_pos := hs
    U_pos := by change 1 ≤ 2 * q.U + 1; omega
    lenAB := by simp [askInst]
    lenBC := by simp [askInst]
    lenAC := by simp [askInst]
    segAB := sAB
    segBC := sBC
    segAC := sAC
    leAB := abs_le_of_mem_subMat hU (hle _ hpre.leX)
    leBC := abs_le_of_mem_subMat hU (hle _ hpre.leY)
    leAC := abs_le_of_mem_maskNeg hF (abs_le_of_mem_subMat hU (hle _ hpre.leV))
    belowAB := by simp only [askInst]; omega
    belowBC := by simp only [askInst]; omega
    belowAC := by simp only [askInst]; omega
    belowRes := by simp only [askInst]; omega
    apartAB := by simp only [askInst]; omega
    apartBC := by simp only [askInst]; omega
    apartAC := by simp only [askInst]; omega }









/-- What the answer of the solver means for the triple of blocks. -/
theorem askPost_of_post {q : PairsInst} {O : List ℤ} {μ μ₅ μ₆ : ℕ → ℤ} {fr fr' s oI oK oJ : ℕ}
    {z : ℤ} (hpre : q.Pre μ fr) (h : findTask.Post (askInst q O fr s oI oK oJ) μ₅ fr' z μ₆) :
    AskPost q O s oI oK oJ (fr + 3 * (s * s)) z μ₆ := by
  obtain ⟨hz, hyes, -⟩ := h
  have hres : fr + 3 * (s * s) = fr + s * s + s * s + s * s := by omega
  by_cases hneg : (blockTri q.n s (2 * (q.U : ℤ) + 1) q.X q.Y q.V O oI oK oJ).HasNegativeTriangle
  · have hone : z = 1 := hz.trans (flag_of hneg)
    obtain ⟨a, b, c, ma, -, mc, hS⟩ := hyes hone
    obtain ⟨hun, hlt⟩ := unmarked_of_neg (O := O) (V := q.V) hpre.leX hpre.leY hS
    exact .inr ⟨hone, a, a.2, b, b.2, c, c.2, hres ▸ ma, hres ▸ mc, hun, hlt⟩
  · exact .inl ⟨hz.trans (flag_of_not hneg), blockDone_of_not hneg⟩

/-- **ask** asks the solver about the triple of blocks at the offsets oI, oK, oJ, and changes no
cell below the free pointer. -/
theorem ask_meets (C : Ctx P₀ R p₀ pCbrt pFill pAsk pSub pCopy pMask T r) {q : PairsInst}
    {μ : ℕ → ℤ} {fr : ℕ} {O : List ℤ} (s oI oK oJ : ℕ) (hpre : q.Pre μ fr) (hO : Seg μ q.out O)
    (lO : O.length = q.n * q.n) (hs : 1 ≤ s) (hin : oI + s ≤ q.n ∧ oK + s ≤ q.n ∧ oJ + s ≤ q.n)
    (hok : (r s (2 * q.U + 1)).Ok lim (fr + 3 * (s * s) + 3) (d + 1))
    (hlim : fr + 4 * (s * s) ≤ lim.space ∧ 2 * (q.U : ℤ) + 1 ≤ lim.word ∧ d + 1 < lim.depth) :
    Meets lim (P₀ ++ R) pAsk d
      [(q.n : ℤ), s, 2 * (q.U : ℤ) + 1, q.x, q.y, q.v, q.out, oI, oK, oJ, fr] μ (askTime T s q.U)
      fun z μ' => Kept μ μ' fr ∧ AskPost q O s oI oK oJ (fr + 3 * (s * s)) z μ' := by
  have hw := hok.space
  have hcells := hok.cells
  (obtain ⟨⟩ := id hpre)
  refine .of_body C.ask ?_
  unfold askBody askTime
  -- area := s * s
  refine Ends.setToThen (s * s : ℕ) ?_
  -- subCopy(n, s, x, oI, oK, fr)
  refine Ends.callToThen (subCopy_meets C.sub C.copy s oI oK fr hpre.segX hpre.lenX (by omega)
    (by omega)) ?_
  rintro _ μ₁ ⟨sX, same₁⟩
  -- subCopy(n, s, y, oK, oJ, fr + area)
  refine Ends.callToThen (subCopy_meets C.sub C.copy s oK oJ (fr + s * s) hpre.segY.keep hpre.lenY
    (by omega) (by omega)) ?_
  rintro _ μ₂ ⟨sY, same₂⟩
  -- subCopy(n, s, v, oI, oJ, fr + area + area)
  refine Ends.callToThen (subCopy_meets C.sub C.copy s oI oJ (fr + s * s + s * s) hpre.segV.keep
    hpre.lenV (by omega) (by omega)) ?_
  rintro _ μ₃ ⟨sV, same₃⟩
  -- subCopy(n, s, out, oI, oJ, fr + area + area + area)
  refine Ends.callToThen (subCopy_meets C.sub C.copy s oI oJ (fr + s * s + s * s + s * s) hO.keep lO
    (by omega) (by omega)) ?_
  rintro _ μ₄ ⟨sO, same₄⟩
  -- mask(area, F, fr + area + area, fr + area + area + area)
  refine Ends.callToThen (mask_meets C.mask (s * s) (2 * (q.U : ℤ) + 1) sV.keep sO
    ⟨by simp, by simp⟩ (abs_le_of_mem_subMat (by positivity) hpre.leV) (by omega) (by omega)) ?_
  rintro _ μ₅ ⟨sM, same₅⟩
  -- The solver is asked about the three matrices.
  refine Ends.callTo (T' := T s (2 * q.U + 1)) (C.sol.meets R (askInst q O fr s oI oK oJ)
    (fr + 3 * (s * s) + 3) (askInst_pre hpre hs sX.keep sY.keep sM) hok) ?_
    (by simp [findTask, askInst, abs_le]; omega)
  rintro z μ₆ hpost
  have same₆ : KeptBut μ₅ μ₆ _ (fr + s * s + s * s + s * s) 3 := hpost.2.2
  exact ⟨by ((try refine Light.SameOn.cell ?_);
                (intro apspMacro_117859_0 apspMacro_117859_1);
                (first
                  |
                    ((((repeat
                              (((with_reducible
                                      rename Light.SameOn _ _ _ => apspMacro_117859_2));
                                ((try
                                      have :=
                                        apspMacro_117859_2 apspMacro_117859_0 (by omega)));
                                (revert apspMacro_117859_2)));
                          (intros);
                          (try simp only [Function.update_apply, Light.wrote] at *)));
                      (omega))
                  |
                    ((simp [] at apspMacro_117859_1);
                      (((repeat
                              (((with_reducible
                                      rename Light.SameOn _ _ _ => apspMacro_117859_3));
                                ((try
                                      have :=
                                        apspMacro_117859_3 apspMacro_117859_0 (by omega)));
                                (revert apspMacro_117859_3)));
                          (intros);
                          (try simp only [Function.update_apply, Light.wrote] at *)));
                      (omega))
                  |
                    ((((repeat
                              (((with_reducible
                                      rename Light.SameOn _ _ _ => apspMacro_117859_4));
                                ((try
                                      have :=
                                        apspMacro_117859_4 apspMacro_117859_0 (by omega)));
                                (revert apspMacro_117859_4)));
                          (intros);
                          (try simp only [Function.update_apply, Light.wrote] at *)));
                      (fail
                          "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                    SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                    its condition K x does not follow from the hypotheses.")))), askPost_of_post hpre hpost⟩

/-! ## The parts of a round -/

variable {q : PairsInst} {s p I K J : ℕ} {O : List ℤ}














/-- advanceStmt goes on to the next triple of blocks. -/
theorem advance_spec {P : Program} {q : PairsInst} {μ : ℕ → ℤ} {fr s p I K J : ℕ} {oI oK oJ z : ℤ}
    (hlt : I < p ∧ K < p ∧ J < p) (hword : (p : ℤ) + 1 ≤ lim.word) :
    Ends lim P d advanceStmt ⟨frame (locals q fr s p I K J oI oK oJ z), μ⟩ 24 fun σ' =>
      ∃ I' K' J', σ' = ⟨frame (locals q fr s p I' K' J' oI oK oJ z), μ⟩ ∧
        Next p I K J I' K' J' := by
  unfold advanceStmt
  -- J := J + 1; if J = p
  refine Ends.setToThen (J + 1 : ℕ) ?_
  refine Ends.iteLast (fun hJ => ?_) (fun hJ => ?_)
  · obtain rfl : J + 1 = p := by simp at hJ; omega
    -- J := 0; K := K + 1; if K = p
    refine Ends.setToThen (0 : ℕ) ?_
    refine Ends.setToThen (K + 1 : ℕ) ?_
    refine Ends.iteLast (fun hK => ?_) (fun hK => ?_)
    · obtain rfl : K = J := by simpa using hK
      -- K := 0; I := I + 1
      refine Ends.setToThen (0 : ℕ) ?_
      refine Ends.setTo (I + 1 : ℕ) ?_
      exact ⟨I + 1, 0, 0, rfl,
        { leI := by omega, ltK := by omega, ltJ := by omega, top := fun _ => ⟨rfl, rfl⟩
          idx := tripleIdx_succ_I K I }⟩
    · have hK' : K ≠ J := by simpa using hK
      exact Ends.skip ⟨I, K + 1, 0, rfl,
        { leI := by omega, ltK := by omega, ltJ := by omega, top := fun h => by omega
          idx := tripleIdx_succ_K J I K }⟩
  · have hJ' : J + 1 ≠ p := by simp at hJ; omega
    exact Ends.skip ⟨I, K, J + 1, rfl,
      { leI := by omega, ltK := by omega, ltJ := by omega, top := fun h => by omega
        idx := tripleIdx_succ_J p I K J }⟩

/-- offStmt puts the offset of block number I into the local dst and changes nothing else.  The text
is used for three pairs of locals, so this is stated like a rule, for any list l of locals and any
Q: h says that Q holds of the state afterwards, and in a proof it is the goal that remains. -/
theorem off_spec {P : Program} {l : List ℤ} {μ : ℕ → ℤ} {dst src : ℕ} {Q : State → Prop} (n s I : ℕ)
    (h : Q ⟨frame (setLocal l dst (blockOff n s I : ℕ)), μ⟩) (hI : I * s < n ∧ s ≤ n)
    (hword : 2 * (n : ℤ) ≤ lim.word) (hN : frame l N = n := by rfl)
    (hS : frame l Side = s := by rfl) (hsrc : frame l src = I := by rfl)
    (hdst : N ≠ dst ∧ Side ≠ dst := by decide) :
    Ends lim P d (offStmt dst src) ⟨frame l, μ⟩ 14 Q := by
  rw [← update_frame_setLocal, blockOff] at h
  generalize frame l = loc at *
  have hN' : ∀ z, Function.update loc dst z N = n := fun z => by
    rw [Function.update_of_ne hdst.1, hN]
  have hS' : ∀ z, Function.update loc dst z Side = s := fun z => by
    rw [Function.update_of_ne hdst.2, hS]
  unfold offStmt
  -- dst := I * s
  refine Ends.setThen ?_ (by simp [hsrc, hS]; omega)
  -- if n < dst + s
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by simp [hsrc, hS, hS', abs_le]; omega)
  · -- dst := n - s
    rw [if_neg (by simp [hsrc, hS, hS', hN'] at hc; omega)] at h
    exact Ends.setLast (by simpa [hS', hN', Nat.cast_sub hI.2] using h)
      (by simp [hS', hN', abs_le]; omega)
  · rw [if_pos (by simp [hsrc, hS, hS', hN'] at hc; omega)] at h
    exact Ends.skip (by simpa [hsrc, hS] using h)

/-- markStmt marks the pair (oI + a, oJ + c), where a and c stand in the solver's answer. -/
theorem mark_spec {P : Program} {μ : ℕ → ℤ} {fr oI oK oJ a c : ℕ} {z : ℤ}
    (ha : μ (fr + 3 * (s * s)) = a) (hc : μ (fr + 3 * (s * s) + 2) = c)
    (hlt : oI + a < q.n ∧ oJ + c < q.n) (hout : q.out + q.n * q.n ≤ fr)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ fr + 3 * (s * s) + 3 ≤ lim.space) :
    Ends lim P d markStmt ⟨frame (locals q fr s p I K J oI oK oJ z), μ⟩ 24 fun σ' =>
      σ' = ⟨frame (locals q fr s p I K J oI oK oJ z),
        Function.update μ (q.out + ((oI + a) * q.n + (oJ + c))) 1⟩ := by
  have hn : q.n ≤ q.n * q.n := Nat.le_mul_self _
  have hidx : (oI + a) * q.n + (oJ + c) < q.n * q.n := Nat.mul_add_lt_mul hlt.1 hlt.2
  have hidxZ : 0 ≤ ((oI : ℤ) + a) * q.n ∧
      ((oI : ℤ) + a) * q.n + ((oJ : ℤ) + c) < (q.n : ℤ) * q.n := by
    exact_mod_cast And.intro (Nat.zero_le _) hidx
  have hres : ((fr : ℤ) + 3 * ((s : ℤ) * s)).toNat = fr + 3 * (s * s) := by omega
  have hres2 : ((fr : ℤ) + 3 * ((s : ℤ) * s) + 2).toNat = fr + 3 * (s * s) + 2 := by omega
  unfold markStmt
  exact Ends.storeTo (q.out + ((oI + a) * q.n + (oJ + c))) 1 rfl
    (by simp [Limits.Addr, abs_le, -abs_mul, hres, hres2, ha, hc]; omega)

/-! ## The invariant -/
















/-- A new mark on a pair with a witness: less is left to do. -/
theorem Progress.mark (h : Progress q s p I K J O) {i j k : ℕ}
    (hlt : i < q.n ∧ j < q.n ∧ k < q.n) (hun : entry q.n O i j ≠ 1)
    (hit : Witness q.n q.X q.Y q.V i k j) :
    Progress q s p I K J (O.set (i * q.n + j) 1) ∧
      todo p I K J (O.set (i * q.n + j) 1) < todo p I K J O := by
  obtain ⟨hi, hj, hk⟩ := hlt
  have hidx : i * q.n + j < O.length := h.marks.len ▸ Nat.mul_add_lt_mul hi hj
  have hcount := count_set_one hidx
    ((h.marks.sound i hi j hj).resolve_right fun hmarked => hun hmarked.1)
  exact ⟨{ h with
    marks := h.marks.set hi hj ⟨k, hk, hit⟩
    done := fun I' hI' K' hK' J' hJ' hbefore => (h.done I' hI' K' hK' J' hJ' hbefore).set hidx },
    by unfold todo; omega⟩

/-- The current triple of blocks is done, and the next one comes: less is left to do. -/
theorem Progress.next (h : Progress q s p I K J O) (hI : I < p)
    (hblock : BlockDone q.n s q.X q.Y q.V O (blockOff q.n s I) (blockOff q.n s K)
      (blockOff q.n s J)) {I' K' J' : ℕ} (hn : Next p I K J I' K' J') :
    Progress q s p I' K' J' O ∧ todo p I' K' J' O < todo p I K J O := by
  have hlt := tripleIdx_lt hI h.ltK h.ltJ
  refine ⟨{ hn with marks := h.marks, done := fun I'' hI'' K'' hK'' J'' hJ'' hbefore => ?_ },
    by unfold todo; rw [hn.idx]; omega⟩
  -- A triple before the next one is a triple before the current one, or the current one.
  rcases Nat.lt_succ_iff_lt_or_eq.1 (hn.idx ▸ hbefore) with hlt' | heq
  · exact h.done I'' hI'' K'' hK'' J'' hJ'' hlt'
  · obtain ⟨rfl, rfl, rfl⟩ := tripleIdx_inj hK'' hJ'' h.ltK h.ltJ heq
    exact hblock













private theorem pairsVar_eq {fr : ℕ} {oI oK oJ z : ℤ} {μ' : ℕ → ℤ} (hO : Seg μ' q.out O)
    (h : Progress q s p I K J O) :
    pairsVar q p ⟨frame (locals q fr s p I K J oI oK oJ z), μ'⟩ = todo p I K J O := by
  rw [hO.eq_readSeg, h.marks.len]
  simp [pairsVar]










/-! ## A round -/

/-- One round keeps the invariant, and afterwards less is left to do. -/
theorem round_spec (C : Ctx P₀ R p₀ pCbrt pFill pAsk pSub pCopy pMask T r) {q : PairsInst}
    {μ : ℕ → ℤ} {fr s : ℕ} (hpre : q.Pre μ fr) (hlim : Lim lim d r q fr s) (hs : 1 ≤ s ∧ s ≤ q.n)
    {σ : State} (hI : PairsInv q μ fr s (blockCount q.n s) σ)
    (hc : ((Light.Cond.lt (v BlockI) (v Blocks))).Holds σ) :
    Ends lim (P₀ ++ R) d (pairsRound pAsk) σ (roundTime T s q.U) fun σ' =>
      PairsInv q μ fr s (blockCount q.n s) σ' ∧
        pairsVar q (blockCount q.n s) σ' < pairsVar q (blockCount q.n s) σ := by
  obtain ⟨I, K, J, O, z₁, z₂, z₃, z, μ', rfl, hk, hO, hP⟩ := hI
  have hIlt : I < blockCount q.n s := by simpa using hc
  have hpn : blockCount q.n s ≤ q.n := blockCount_le hs.1
  have hw := hlim.ok.space
  have hword := hlim.word
  have hcells := hlim.cells
  have hdepth := hlim.depth
  have hout := hpre.belowOut
  have hlen := hP.marks.len
  have bI := blockOff_add_le hs.2 I
  have bK := blockOff_add_le hs.2 K
  have bJ := blockOff_add_le hs.2 J
  rw [pairsVar_eq hO hP]
  unfold pairsRound roundTime
  -- oI, oK, oJ := the offsets of the three blocks
  refine Ends.next _ (off_spec q.n s I ?_ ⟨(lt_blockCount_iff hs.1 I).1 hIlt, hs.2⟩ (by omega))
  refine Ends.next _ (off_spec q.n s K ?_ ⟨(lt_blockCount_iff hs.1 K).1 hP.ltK, hs.2⟩ (by omega))
  refine Ends.next _ (off_spec q.n s J ?_ ⟨(lt_blockCount_iff hs.1 J).1 hP.ltJ, hs.2⟩ (by omega))
  -- reply := ask(n, s, F, x, y, v, out, oI, oK, oJ, fr)
  refine Ends.callToThen (ask_meets C s (blockOff q.n s I) (blockOff q.n s K) (blockOff q.n s J)
    hpre.keep hO hlen hs.1 ⟨bI, bK, bJ⟩ hlim.ok (by omega)) ?_
  rintro reply μ'' ⟨hkAsk, hpost⟩
  have hO'' : Seg μ'' q.out O := hO.keep
  -- if reply = 1
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
  · -- The solver has found an unmarked pair with a witness: it is marked.
    obtain ⟨-, a, ha, b, hb, c, hc, ma, mc, hun, hwit⟩ :=
      hpost.resolve_left fun h => by simp [h.1] at hyes
    obtain ⟨hP', hless⟩ := hP.mark (k := blockOff q.n s K + b) (by omega) hun hwit
    have hidx := Nat.mul_add_lt_mul (show blockOff q.n s I + a < q.n by omega)
      (show blockOff q.n s J + c < q.n by omega)
    have hO' := hO''.update_in (hlen ▸ hidx) 1
    refine (mark_spec ma mc (by omega) hout ⟨hw, by omega⟩).mono (by first
                                                                         |
                                                                           ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
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
    rintro _ rfl
    exact ⟨⟨I, K, J, _, _, _, _, _, _, rfl, by ((try refine Light.SameOn.cell ?_);
                                                     (intro apspMacro_126961_0 apspMacro_126961_1);
                                                     (first
                                                       |
                                                         ((((repeat
                                                                   (((with_reducible
                                                                           rename Light.SameOn _ _ _ => apspMacro_126961_2));
                                                                     ((try
                                                                           have :=
                                                                             apspMacro_126961_2 apspMacro_126961_0 (by omega)));
                                                                     (revert apspMacro_126961_2)));
                                                               (intros);
                                                               (try simp only [Function.update_apply, Light.wrote] at *)));
                                                           (omega))
                                                       |
                                                         ((simp [] at apspMacro_126961_1);
                                                           (((repeat
                                                                   (((with_reducible
                                                                           rename Light.SameOn _ _ _ => apspMacro_126961_3));
                                                                     ((try
                                                                           have :=
                                                                             apspMacro_126961_3 apspMacro_126961_0 (by omega)));
                                                                     (revert apspMacro_126961_3)));
                                                               (intros);
                                                               (try simp only [Function.update_apply, Light.wrote] at *)));
                                                           (omega))
                                                       |
                                                         ((((repeat
                                                                   (((with_reducible
                                                                           rename Light.SameOn _ _ _ => apspMacro_126961_4));
                                                                     ((try
                                                                           have :=
                                                                             apspMacro_126961_4 apspMacro_126961_0 (by omega)));
                                                                     (revert apspMacro_126961_4)));
                                                               (intros);
                                                               (try simp only [Function.update_apply, Light.wrote] at *)));
                                                           (fail
                                                               "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                         SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                         its condition K x does not follow from the hypotheses.")))), hO', hP'⟩,
      by rw [pairsVar_eq hO' hP']; exact hless⟩
  · -- The triple of blocks is done: the next one comes.
    have hblock := (hpost.resolve_right fun h => hno (by simp [h.1])).2
    refine (advance_spec ⟨hIlt, hP.ltK, hP.ltJ⟩ (by omega)).mono (by first
                                                                         |
                                                                           ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
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
    rintro _ ⟨I', K', J', rfl, hnext⟩
    obtain ⟨hP', hless⟩ := hP.next hIlt hblock hnext
    exact ⟨⟨I', K', J', O, _, _, _, _, μ'', rfl, by ((try refine Light.SameOn.cell ?_);
                                                           (intro apspMacro_127410_0 apspMacro_127410_1);
                                                           (first
                                                             |
                                                               ((((repeat
                                                                         (((with_reducible
                                                                                 rename Light.SameOn _ _ _ => apspMacro_127410_2));
                                                                           ((try
                                                                                 have :=
                                                                                   apspMacro_127410_2 apspMacro_127410_0 (by omega)));
                                                                           (revert apspMacro_127410_2)));
                                                                     (intros);
                                                                     (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                 (omega))
                                                             |
                                                               ((simp [] at apspMacro_127410_1);
                                                                 (((repeat
                                                                         (((with_reducible
                                                                                 rename Light.SameOn _ _ _ => apspMacro_127410_3));
                                                                           ((try
                                                                                 have :=
                                                                                   apspMacro_127410_3 apspMacro_127410_0 (by omega)));
                                                                           (revert apspMacro_127410_3)));
                                                                     (intros);
                                                                     (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                 (omega))
                                                             |
                                                               ((((repeat
                                                                         (((with_reducible
                                                                                 rename Light.SameOn _ _ _ => apspMacro_127410_4));
                                                                           ((try
                                                                                 have :=
                                                                                   apspMacro_127410_4 apspMacro_127410_0 (by omega)));
                                                                           (revert apspMacro_127410_4)));
                                                                     (intros);
                                                                     (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                 (fail
                                                                     "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                               SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                               its condition K x does not follow from the hypotheses.")))), hO'', hP'⟩,
      by rw [pairsVar_eq hO'' hP']; exact hless⟩

/-! ## The host -/

/-- countStmt puts p = ⌈n/s⌉ into its local and changes nothing else.  It is stated like off_spec,
for any list l of locals and any Q. -/
theorem count_spec {P : Program} {l : List ℤ} {μ : ℕ → ℤ} {Q : State → Prop} (n s : ℕ)
    (h : Q ⟨frame (setLocal l Blocks (blockCount n s : ℕ)), μ⟩) (hs : 1 ≤ s ∧ s ≤ n)
    (hword : 2 * (n : ℤ) + 1 ≤ lim.word) (hN : frame l N = n := by rfl)
    (hS : frame l Side = s := by rfl) :
    Ends lim P d countStmt ⟨frame l, μ⟩ (10 * blockCount n s + 8) Q := by
  have hpn : blockCount n s ≤ n := blockCount_le hs.1
  rw [← update_frame_setLocal] at h
  generalize frame l = loc at *
  unfold countStmt
  -- p := 0
  refine Ends.setThen ?_
  -- while p * s < n: p := p + 1
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc Blocks j, μ⟩) (blockCount n s)
    (by simp) ?round ?done
  case round =>
    rintro j _ hj rfl
    have hjs : j * s < n := (lt_blockCount_iff hs.1 j).1 hj
    exact ⟨by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                  Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                  reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                  Nat.cast_zero, Nat.cast_one, N, Side, Blocks, hS, abs_le]; omega,
      by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
           Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
           reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
           Nat.cast_zero, Nat.cast_one, N, Side, Blocks, hN, hS]; omega,
      by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
           Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
           reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
           Nat.cast_zero, Nat.cast_one, Stmt.BlockSafe, abs_le]; omega, by simp⟩
  case done =>
    rintro _ rfl
    have hlow := le_blockCount_mul (n := n) hs.1
    have hhigh := blockCount_mul_lt (n := n) hs.1
    exact ⟨by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                  Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                  reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                  Nat.cast_zero, Nat.cast_one, N, Side, Blocks, hS, abs_le]; omega,
      by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
           Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
           reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
           Nat.cast_zero, Nat.cast_one, N, Side, Blocks, hN, hS]; omega, h⟩

/-- The list of marks is the list of flags of the task, when it holds the right flag for every
pair. -/
theorem eq_pairFlags {n : ℕ} {X Y V O : List ℤ} (lO : O.length = n * n)
    (h : ∀ i < n, ∀ j < n, entry n O i j = flag (PairHit n X Y V i j)) :
    O = pairFlags n X Y V := by
  refine List.ext_getElem (by simp [pairFlags, lO]) fun t ht _ => ?_
  obtain ⟨i, hi, j, hj, rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul (lO ▸ ht)
  rw [← List.getD_eq_getElem _ 0 ht, ← entry, h i hi j hj]
  simp only [pairFlags, List.getElem_map, List.getElem_range, PairHit, Witness,
    Nat.mul_add_div_of_lt hj,
    Nat.mul_add_mod_of_lt hj]

/-- **When no triple of blocks is left, the marks are the answer.** -/
theorem Progress.complete (h : Progress q s (blockCount q.n s) (blockCount q.n s) K J O)
    (hs : 1 ≤ s ∧ s ≤ q.n) : O = pairFlags q.n q.X q.Y q.V := by
  obtain ⟨rfl, rfl⟩ := h.top rfl
  exact eq_pairFlags h.marks.len fun i hi j hj => h.marks.complete hs.1 hs.2
    (fun I' hI' K' hK' J' hJ' =>
      h.done I' hI' K' hK' J' hJ' (tripleIdx_top _ ▸ tripleIdx_lt hI' hK' hJ'))
    hi hj

/-- At the beginning all p³ triples of blocks and all pairs are left. -/
private theorem todo_start (p m : ℕ) : todo p 0 0 0 (List.replicate m 0) = p * p * p + m := by
  simp [todo, tripleIdx]

/-- At the beginning no pair is marked, and no triple of blocks has been visited. -/
theorem progress_start (q : PairsInst) (s : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    Progress q s p 0 0 0 (List.replicate (q.n * q.n) 0) :=
  { leI := by omega
    ltK := hp
    ltJ := hp
    top := fun _ => ⟨rfl, rfl⟩
    marks := marks_replicate ..
    done := fun I' _ K' _ J' _ hbefore => absurd hbefore (by simp [tripleIdx]) }

/-- What allPairs needs covers what the rounds need. -/
private theorem lim_of_ok {fr : ℕ} (hok : (pairsNeed r q.n q.U).Ok lim fr d) :
    Lim lim d r q fr (cbrtLeast q.n) := by
  have hword := hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  simp only [pairsNeed] at hword hcells hdepth
  exact
    { ok := by refine hok.mono ?_ ?_ ?_ <;> simp only [pairsNeed] <;> omega
      cells := by omega
      word := by omega
      depth := by omega }

/-- A round, with the test of the loop (4 steps). -/
private theorem roundTime_le (T : ℕ → ℕ → ℕ) (s U : ℕ) :
    roundTime T s U + 4 ≤ 220 * s ^ 2 + 250 + T s (2 * U + 1) := by
  have hs : s ≤ s ^ 2 := Nat.le_self_pow (by norm_num) s
  have hcopy : s * (16 * s + 31) = 16 * s ^ 2 + 31 * s := by ring
  unfold roundTime askTime subCopyTime maskTime
  rw [hcopy, ← pow_two]
  omega

/-- The steps of allPairs add up to at most pairsTime: cbrtCeil takes 12 s steps, countStmt 10 p,
fill 13 n², the other statements before the rounds 56 in all, and there are at most p³ + n² rounds,
each with the test of the loop. -/
private theorem time_le (T : ℕ → ℕ → ℕ) {n s p : ℕ} (U : ℕ) (hsn : s ≤ n) (hpn : p ≤ n) :
    12 * s + 10 * p + 13 * (n * n) + 56 + ((p * p * p + n * n) * (roundTime T s U + 4) + 4) ≤
      40 * n ^ 2 + 80 + (p ^ 3 + n ^ 2) * (220 * s ^ 2 + 250 + T s (2 * U + 1)) := by
  have hn : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  have hrounds := Nat.mul_le_mul_left (p ^ 3 + n ^ 2) (roundTime_le T s U)
  rw [show p * p * p = p ^ 3 by ring, ← pow_two]
  omega

/-- **allPairs** solves the task. -/
theorem pairs_spec (C : Ctx P₀ R p₀ pCbrt pFill pAsk pSub pCopy pMask T r) {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : q.Pre μ fr) (hok : (pairsNeed r q.n q.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (pairsBody pCbrt pFill pAsk) ⟨frame (pairsTask.args q ++ [(fr : ℤ)]), μ⟩
      (pairsTime T q.n q.U) fun σ' => pairsTask.Post q μ fr (σ'.loc 0) σ'.mem := by
  have hlim := lim_of_ok hok
  have hs : 1 ≤ cbrtLeast q.n ∧ cbrtLeast q.n ≤ q.n :=
      ⟨one_le_cbrtLeast hpre.n_pos, cbrtLeast_le_self q.n⟩
  refine Ends.mono ?_ (time_le T q.U hs.2 (blockCount_le hs.1)) fun _ h => h
  have hw := hlim.ok.space
  have hword := hlim.word
  have hcells := hlim.cells
  have hdepth := hlim.depth
  have hout := hpre.belowOut
  have hP := progress_start q (cbrtLeast q.n) (blockCount_pos hs.1 hpre.n_pos)
  change Ends _ _ _ _ ⟨frame [(q.n : ℤ), q.U, q.x, q.y, q.v, q.out, fr], μ⟩ _ _
  unfold pairsBody
  -- s := cbrtCeil(n)
  refine Ends.callToThen (cbrtCeil_meets (n := q.n) C.cbrt μ (by push_cast; omega)) ?_
  rintro _ μ₀ ⟨rfl, hμ⟩
  obtain rfl : μ = μ₀ := hμ.symm
  unfold cbrtCeilTime
  generalize cbrtLeast q.n = s at *
  -- p := ⌈n/s⌉
  refine Ends.next _ (count_spec q.n s ?_ hs (by omega))
  -- large := 2U + 1; answer := fr + 3 s²
  refine Ends.setToThen (2 * (q.U : ℤ) + 1) ?_
  refine Ends.setToThen (fr + 3 * (s * s) : ℕ) ?_
  -- fill(out, n², 0): no pair is marked
  refine Ends.callToThen (fill_meets C.fill (dst := q.out) (n := q.n * q.n) (x := 0) hw (by omega))
    ?_
  rintro z μ₁ ⟨hO, hrest⟩
  -- I := 0; K := 0; J := 0
  refine Ends.setToThen (0 : ℕ) ?_
  refine Ends.setToThen (0 : ℕ) ?_
  refine Ends.setToThen (0 : ℕ) ?_
  -- The rounds.
  refine Ends.whileVariant (PairsInv q μ fr s (blockCount q.n s)) (pairsVar q (blockCount q.n s))
    (roundTime T s q.U)
    ⟨0, 0, 0, _, 0, 0, 0, z, μ₁, rfl, by ((try refine Light.SameOn.cell ?_);
                                                (intro apspMacro_134162_0 apspMacro_134162_1);
                                                (first
                                                  |
                                                    ((((repeat
                                                              (((with_reducible
                                                                      rename Light.SameOn _ _ _ => apspMacro_134162_2));
                                                                ((try
                                                                      have :=
                                                                        apspMacro_134162_2 apspMacro_134162_0 (by omega)));
                                                                (revert apspMacro_134162_2)));
                                                          (intros);
                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                      (omega))
                                                  |
                                                    ((simp [] at apspMacro_134162_1);
                                                      (((repeat
                                                              (((with_reducible
                                                                      rename Light.SameOn _ _ _ => apspMacro_134162_3));
                                                                ((try
                                                                      have :=
                                                                        apspMacro_134162_3 apspMacro_134162_0 (by omega)));
                                                                (revert apspMacro_134162_3)));
                                                          (intros);
                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                      (omega))
                                                  |
                                                    ((((repeat
                                                              (((with_reducible
                                                                      rename Light.SameOn _ _ _ => apspMacro_134162_4));
                                                                ((try
                                                                      have :=
                                                                        apspMacro_134162_4 apspMacro_134162_0 (by omega)));
                                                                (revert apspMacro_134162_4)));
                                                          (intros);
                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                      (fail
                                                          "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                    SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                    its condition K x does not follow from the hypotheses.")))), hO, hP⟩
    (fun _ _ => ⟨trivial, trivial⟩) (fun σ hI hc => round_spec C hpre hlim hs hI hc) ?done ?time
  case done =>
    rintro _ ⟨I, K, J, O, _, _, _, _, μ', rfl, hk, hO', hP'⟩ hc
    obtain rfl : I = blockCount q.n s := by have := hP'.leI; simp at hc; omega
    exact ⟨hP'.complete hs ▸ hO', hk⟩
  case time =>
    change pairsVar q _ ⟨frame (locals q fr s (blockCount q.n s) 0 0 0 0 0 0 z), μ₁⟩ * _ + _ ≤ _
    rw [pairsVar_eq hO hP, todo_start]
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

/-! ## The need -/

/-- The need of allPairs is polynomially bounded if the need of the solver is. -/
theorem polyNeed_pairs (hr : PolyNeed r) : PolyNeed (pairsNeed r) := by
  unfold pairsNeed
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
                  | apply Scale.SoftO.of_forall_le cbrtLeast_le_self
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
                                | apply Scale.SoftO.of_forall_le cbrtLeast_le_self
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
                          | apply Scale.SoftO.of_forall_le cbrtLeast_le_self
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
                  | apply Scale.SoftO.of_forall_le cbrtLeast_le_self
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)))

end Pairs

open Pairs

/-- **The middle step of [VW18, Theorem 4.2]: all pairs with a witness, from finding a negative
triangle.** -/
theorem isHost_pairs : IsHost findTask pairsTask pairsTime pairsNeed := by
  refine ⟨fun P p T r hsol => ⟨pairsProcs P.length p, P.length + 6, ?_⟩,
    fun r hr => polyNeed_pairs hr⟩
  refine ⟨pairsBody (P.length + 3) (P.length + 1) (P.length + 5), by simp [pairsProcs],
    fun R' lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact pairs_spec (pSub := P.length + 2) (pCopy := P.length) (pMask := P.length + 4)
    { sol := hsol
      sub := by simp [pairsProcs]
      copy := by simp [pairsProcs]
      mask := by simp [pairsProcs]
      cbrt := by simp [pairsProcs]
      fill := by simp [pairsProcs]
      ask := by simp [pairsProcs] } hpre hok

end Light.Sec3

end
end

section


/-!
# Two passes over an array, for the (min,+)-product found bit by bit

Two routines of the host for [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).

addc(len, x, src, dst): dst[i] := src[i] + x, in at most 19 len + 6 steps (addc_meets).
bump(len, x, fl, lo): lo[i] := lo[i] + x (1 − fl[i]), in at most 30 len + 6 steps: where the flag
is 0 the entry grows by x (bump_meets).
Both change no other cell.  Each is one pass, so each proof only says what round j reads.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Pass









end Pass











/-- **addc** writes the list with x added to every entry to dst and changes nothing else. -/
theorem addc_meets {p : ℕ} (hp : P[p]? = some addcBody) {μ : ℕ → ℤ} {src len : ℕ} {L : List ℤ}
    (x : ℤ) (dst : ℕ) (hL : Seg μ src L) (hlen : L.length = len)
    (hsep : Apart src len dst len)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ src + len ≤ lim.space ∧ dst + len ≤ lim.space)
    (hfits : ∀ y ∈ L, |y + x| ≤ lim.word) :
    Meets lim P p d [(len : ℤ), x, src, dst] μ (19 * len + 6) fun _ μ' =>
      Seg μ' dst (L.map (· + x)) ∧ SameOutside μ μ' dst len := by
  subst hlen
  obtain ⟨hw, hsrc, hdst⟩ := hlim
  set f : ℕ → ℤ := fun i => L.getD i 0 + x with hf
  have hfi : ∀ i (hi : i < L.length), f i = L[i] + x := fun i hi => by
    rw [hf]
    simp only [List.getD_eq_getElem _ _ hi]
  refine .of_body hp (Ends.pass f (fun j hj => ?_) ?_ hw hdst rfl rfl)
  · -- round j reads src[j], which lies outside the cells that are written
    have hread : wrote μ dst f j (src + j) = L[j] := (wrote_rest (by omega)).trans (hL j hj)
    have hfitsj := abs_le.1 (hfits _ (List.getElem_mem hj))
    rw [update_frame_setLocal]
    simp [Limits.Addr, abs_le, hread, hfi j hj]; omega
  · dsimp only
    refine ⟨fun i hi => ?_, sameOutside_wrote le_rfl⟩
    have hi' : i < L.length := by simpa using hi
    rw [wrote_done hi', List.getElem_map, hfi i hi']

/-- **bump** adds x (1 − flag) to every entry of the list at lo and changes nothing else.  The flags
are 0 or 1, and V bounds the entries. -/
theorem bump_meets {p : ℕ} (hp : P[p]? = some bumpBody) {μ : ℕ → ℤ} {fl lo len : ℕ} {F L : List ℤ}
    {V : ℤ} (x : ℤ) (hF : Seg μ fl F) (hL : Seg μ lo L) (hlen : F.length = len ∧ L.length = len)
    (hsep : Apart fl len lo len)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ fl + len ≤ lim.space ∧ lo + len ≤ lim.space)
    (hflag : ∀ f ∈ F, f = 0 ∨ f = 1) (hle : AbsLe L V) (hfits : |x| + V ≤ lim.word ∧ 1 ≤ lim.word) :
    Meets lim P p d [(len : ℤ), x, fl, lo] μ (30 * len + 6) fun _ μ' =>
      Seg μ' lo (List.zipWith (fun l f => l + x * (1 - f)) L F) ∧ SameOutside μ μ' lo len := by
  obtain ⟨lF, lL⟩ := hlen
  obtain ⟨hw, hfl, hlo⟩ := hlim
  set f : ℕ → ℤ := fun i => L.getD i 0 + x * (1 - F.getD i 0) with hf
  have hfi : ∀ i (hF : i < F.length) (hL : i < L.length), f i = L[i] + x * (1 - F[i]) :=
    fun i hF hL => by
      rw [hf]
      simp only [List.getD_eq_getElem _ _ hF, List.getD_eq_getElem _ _ hL]
  refine .of_body hp (Ends.pass f (fun j hj => ?_) ?_ hw hlo rfl rfl)
  · -- round j reads the flag fl[j], which is never written, and lo[j], which it then overwrites
    have hreadF : wrote μ lo f j (fl + j) = F[j] := (wrote_rest (by omega)).trans (hF j (by omega))
    have hreadL : wrote μ lo f j (lo + j) = L[j] := (wrote_rest (by omega)).trans (hL j (by omega))
    have hentry := abs_le.1 (hle.getElem (i := j) (by omega))
    have hx := abs_le.1 (le_refl |x|)
    rw [update_frame_setLocal]
    rcases hflag _ (List.getElem_mem (show j < F.length by omega)) with h | h
    all_goals
      simp [Limits.Addr, abs_le, -abs_mul, hreadF, hreadL, hfi j (by omega) (by omega), h]; omega
  · dsimp only
    exact ⟨seg_wrote (by simp [lF, lL]) fun i hi => by
      rw [List.getElem_zipWith, hfi], sameOutside_wrote le_rfl⟩

end Light.Sec3

end
end

section


/-!
# The entries of a (min,+)-product, found bit by bit

Theorem 21(b), after [VW18, Theorem 4.2]: the (min,+)-product is computed
by a binary search for all entries at once.  An entry `c` with `-2U ≤ c ≤ 2U` is approached from
below: `bitLo U t c` is `c` with the lowest `t` bits of `c + 2U` cleared.

* The search starts at `t = R`, where `4U < 2^R`, with `-2U` (`bitLo_top`), and it ends at `t = 0`
  with `c` (`bitLo_zero`).
* One round goes from `t + 1` to `t`: it asks whether `c < bitLo U (t + 1) c + 2^t` and adds `2^t`
  if not (`bitLo_step`).
* The question is whether the pair `(i, j)` has a witness: `c` is below a number exactly if one of
  the sums `A[i,k] + B[k,j]` is (`exists_sum_lt_iff`).  So one round for all entries is one call of
  a routine that finds all pairs with a witness.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- Some sum `A[i,k] + B[k,j]` is below `z` exactly if the entry `(i, j)` of the product is. -/
theorem exists_sum_lt_iff {n : ℕ} (hn : 1 ≤ n) (A B : List ℤ) (i j : ℕ) (z : ℤ) :
    (∃ k < n, entry n A i k + entry n B k j < z) ↔ minPlusEntry n A B i j < z := by
  constructor
  · rintro ⟨k, hk, h⟩
    exact (minPlusEntry_le n A B i j hk).trans_lt h
  · intro h
    obtain ⟨k, hk, he⟩ := exists_minPlusEntry_eq hn A B i j
    exact ⟨k, hk, he ▸ h⟩




/-- With no bit cleared the number is `c`: the end of the search. -/
theorem bitLo_zero {U c : ℤ} (h : -(2 * U) ≤ c) : bitLo U 0 c = c := by
  rw [bitLo, pow_zero, Nat.div_one, Nat.mul_one, Int.toNat_of_nonneg (by linarith)]
  ring

/-- With all bits cleared the number is `-2U`: the start of the search. -/
theorem bitLo_top {U c : ℤ} {R : ℕ} (h : c + 2 * U < 2 ^ R) : bitLo U R c = -(2 * U) := by
  have hlt : (c + 2 * U).toNat < 2 ^ R := by
    rw [Int.toNat_lt' (by positivity)]
    exact_mod_cast h
  simp [bitLo, Nat.div_eq_of_lt hlt]

/-- The search never goes below `-2U`. -/
theorem le_bitLo (U : ℤ) (t : ℕ) (c : ℤ) : -(2 * U) ≤ bitLo U t c :=
  le_add_of_nonneg_right (Int.natCast_nonneg _)

/-- The search never goes above `c`. -/
theorem bitLo_le {U c : ℤ} (h : -(2 * U) ≤ c) (t : ℕ) : bitLo U t c ≤ c := by
  have hle : (c + 2 * U).toNat / 2 ^ t * 2 ^ t ≤ (c + 2 * U).toNat := Nat.div_mul_le_self _ _
  have hcast : ((c + 2 * U).toNat : ℤ) = c + 2 * U := Int.toNat_of_nonneg (by linarith)
  rw [bitLo]
  linarith [Int.ofNat_le.2 hle]








































end ThreeSumApsp.Spec

end
end

section


/-!
# The (min,+)-product from "all pairs", bit by bit

Theorem 21(b), after [VW18, Theorem 4.2].  The host below computes the
(min,+)-product over an arbitrary solver of the task "all pairs": for three matrices X, Y, V, which
pairs (i, j) have X[i,k] + Y[k,j] < V[i,j] for some k.

mp(n, U, a, b, c, fr).  All entries of the product lie between −2U and 2U.  The output array starts
as −2U everywhere.  Let R be least with 2^R > 4U; the powers 1, 2, …, 2^(R−1) are written to the R
cells from fr while R is found by doubling.  For t = R − 1, …, 0: V := lo + 2^t (the n² cells from
fr + R), the solver writes its flags to the next n² cells, and lo grows by 2^t where the flag is 0.
Before the round for t, lo ≤ C[i,j] < lo + 2^(t+1): lo is C[i,j] with the lowest t + 1 bits of
C[i,j] + 2U cleared (lows x (t + 1)).  The entries of V have absolute value at most 6U.

The result is isHost_mp : IsHost pairsTask mpTask mpTime mpNeed.  First the lists: the lower bounds
lows x t, which start as −2U (lows_top), end as the product (lows_zero), and change in a round as
bump changes them (lows_round, from bitLo_step).  Then the program: the powers of two (powers_spec),
a round (round_spec, with the invariant Inv), all rounds (rounds_spec), the host (mp_spec).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The program -/




namespace Mp























end Mp

























































namespace Mp

/-! ## The number of rounds -/

/-- The powers of two below 2^R are at most 4U. -/
theorem pow_range {U i : ℕ} (hU : 1 ≤ U) (hi : i < mpRounds U) :
    0 < (2 : ℤ) ^ i ∧ (2 : ℤ) ^ i ≤ 4 * U := by
  have hle : 2 ^ i ≤ 4 * U := Nat.pow_le_of_le_log (by omega) (by simp only [mpRounds] at hi; omega)
  exact ⟨by positivity, by exact_mod_cast hle⟩

/-- 2^R is above 4U. -/
theorem lt_pow_rounds (U : ℕ) : 4 * (U : ℤ) < 2 ^ mpRounds U := by
  exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (4 * U)

/-! ## The lists of a round -/

variable {x : MatInst} {μ : ℕ → ℤ} {fr : ℕ}











@[simp] theorem length_lows (x : MatInst) (t : ℕ) : (lows x t).length = x.n * x.n := by
  simp [lows, length_minPlusList]

@[simp] theorem length_asked (x : MatInst) (t : ℕ) : (asked x t).length = x.n * x.n := by
  simp [asked]

@[simp] theorem length_flags (x : MatInst) (t : ℕ) : (flags x t).length = x.n * x.n := by
  simp [flags, pairFlags]

/-- An entry of the lower bounds. -/
theorem getElem_lows (x : MatInst) (t q : ℕ) (hq : q < (lows x t).length) :
    (lows x t)[q] = bitLo x.U t (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n)) := by
  simp [lows, minPlusList]

/-- The entries of the product lie between −2U and 2U. -/
theorem entry_range (hpre : x.Pre μ fr) (i j : ℕ) :
    -(2 * (x.U : ℤ)) ≤ minPlusEntry x.n x.A x.B i j ∧ minPlusEntry x.n x.A x.B i j ≤ 2 * x.U :=
  abs_le.1 (abs_minPlusEntry_le hpre.n_pos (by positivity) hpre.leA hpre.leB i j)

/-- The lower bounds lie between −2U and 2U. -/
theorem lows_range (hpre : x.Pre μ fr) (t q : ℕ) (hq : q < (lows x t).length) :
    -(2 * (x.U : ℤ)) ≤ (lows x t)[q] ∧ (lows x t)[q] ≤ 2 * x.U := by
  rw [getElem_lows]
  have hentry := entry_range hpre (q / x.n) (q % x.n)
  exact ⟨le_bitLo _ _ _, (bitLo_le hentry.1 _).trans hentry.2⟩

/-- At the beginning all lower bounds are −2U. -/
theorem lows_top (hpre : x.Pre μ fr) :
    lows x (mpRounds x.U) = List.replicate (x.n * x.n) (-(2 * (x.U : ℤ))) := by
  refine List.ext_getElem (by simp) fun q hq _ => ?_
  rw [getElem_lows, List.getElem_replicate]
  exact bitLo_top (by linarith [(entry_range hpre (q / x.n) (q % x.n)).2, lt_pow_rounds x.U])

/-- At the end the lower bounds are the product. -/
theorem lows_zero (hpre : x.Pre μ fr) : lows x 0 = minPlusList x.n x.A x.B := by
  refine List.ext_getElem (by simp [length_minPlusList]) fun q hq _ => ?_
  rw [getElem_lows, bitLo_zero (entry_range hpre _ _).1]
  simp [minPlusList]

/-- A flag of the round for t: is the entry of the product below the lower bound plus 2^t? -/
theorem getElem_flags (hpre : x.Pre μ fr) (t q : ℕ) (hq : q < (flags x t).length) :
    (flags x t)[q] = flag (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n) <
      bitLo x.U (t + 1) (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n)) + 2 ^ t) := by
  have hq' : q < x.n * x.n := by simpa using hq
  have hV : (asked x t).getD q 0 =
      bitLo x.U (t + 1) (minPlusEntry x.n x.A x.B (q / x.n) (q % x.n)) + 2 ^ t := by
    rw [List.getD_eq_getElem _ _ (by simpa using hq')]
    simp [asked, getElem_lows]
  simp only [flags, pairFlags, List.getElem_map, List.getElem_range, hV]
  exact flag_congr (exists_sum_lt_iff hpre.n_pos x.A x.B (q / x.n) (q % x.n) _)

/-- **One round**: each lower bound grows by 2^t where the flag is 0. -/
theorem lows_round (hpre : x.Pre μ fr) (t : ℕ) :
    List.zipWith (fun l f => l + (2 : ℤ) ^ t * (1 - f)) (lows x (t + 1)) (flags x t) =
      lows x t := by
  refine List.ext_getElem (by simp) fun q _ _ => ?_
  rw [List.getElem_zipWith, getElem_flags hpre, getElem_lows, getElem_lows,
    bitLo_step (entry_range hpre _ _).1 t]

/-- A flag is 0 or 1. -/
theorem flags_eq_zero_or_one (x : MatInst) (t : ℕ) : ∀ f ∈ flags x t, f = 0 ∨ f = 1 := by
  intro f hf
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hf
  have := flag_mem (∃ k < x.n, x.A.getD (q / x.n * x.n + k) 0 + x.B.getD (k * x.n + q % x.n) 0 <
    (asked x t).getD q 0)
  omega

/-- The lower bounds have absolute value at most 2U. -/
theorem absLe_lows (hpre : x.Pre μ fr) (t : ℕ) : AbsLe (lows x t) (2 * x.U) := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
  exact abs_le.2 (lows_range hpre t q hq)

/-- The entries of V have absolute value at most 6U. -/
theorem abs_asked_le (hpre : x.Pre μ fr) {t : ℕ} (ht : t < mpRounds x.U) :
    ∀ y ∈ lows x (t + 1), |y + (2 : ℤ) ^ t| ≤ 6 * (x.U : ℤ) := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
  have hpow := pow_range hpre.U_pos ht
  have hrange := lows_range hpre (t + 1) q hq
  exact abs_le.2 ⟨by omega, by omega⟩

/-! ## The surroundings -/

variable {P₀ R₀ : Program} {pPairs pFill pAddc pBump : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {lim : Limits} {d : ℕ}


















private theorem lim_of_ok (hok : (mpNeed r x.n x.U).Ok lim fr d) : Lim lim d r x fr where
  solver := le_trans (by exact_mod_cast le_max_left _ _) hok.word
  word := le_trans (by exact_mod_cast le_max_right (r x.n (6 * x.U)).word (8 * x.U + 1)) hok.word
  cells := hok.cells
  space := hok.space
  depth := hok.depth











/-! ## Before the rounds -/

/-- mpConsts computes the five numbers. -/
theorem consts_spec {P : Program} (hpre : x.Pre μ fr) (hlim : Lim lim d r x fr) :
    Ends lim P d mpConsts ⟨frame [x.n, x.U, x.a, x.b, x.c, fr], μ⟩ 20 fun σ' =>
      σ' = ⟨frame (consts x fr), μ⟩ := by
  have hcells := hlim.cells
  ((obtain ⟨⟩ := id hlim); (obtain ⟨⟩ := id hpre))
  unfold mpConsts
  refine Ends.setToThen (x.n * x.n : ℕ) ?_
  refine Ends.setToThen (2 * x.U : ℕ) ?_
  refine Ends.setToThen (4 * x.U : ℕ) ?_
  refine Ends.setToThen (-(2 * (x.U : ℤ))) ?_
  exact Ends.setTo (6 * x.U : ℕ) rfl

/-- mpPowers finds R and writes the powers of two to the R cells from fr. -/
theorem powers_spec {P : Program} (hpre : x.Pre μ fr) (hlim : Lim lim d r x fr) :
    Ends lim P d mpPowers ⟨frame (consts x fr), μ⟩ (19 * mpRounds x.U + 10) fun σ' =>
      σ' = ⟨frame (consts x fr ++ [(mpRounds x.U : ℤ), 2 ^ mpRounds x.U]),
        wrote μ fr (fun i => 2 ^ i) (mpRounds x.U)⟩ := by
  have hcells := hlim.cells
  (obtain ⟨⟩ := id hlim)
  unfold mpPowers
  -- count := 0; power := 1
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
          (2 ^ 0)
            -- while power ≤ 4U: mem[fr + count] := power; count := count + 1; power := power + power
            
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
  -- while power ≤ 4U: mem[fr + count] := power; count := count + 1; power := power + power
  refine Ends.whileBlock (fun i σ => σ = ⟨frame (consts x fr ++ [(i : ℤ), 2 ^ i]),
    wrote μ fr (fun i => 2 ^ i) i⟩) (mpRounds x.U) (by rw [wrote_zero]; rfl) ?round ?done
  case round =>
    rintro i _ hi rfl
    have hpow := pow_range hpre.U_pos hi
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, by (((try have := Light.Std.space_le (by assumption)));
                                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), ?_⟩
    rw [← wrote_succ]
    simp [update_frame_setLocal, pow_succ, mul_two]
  case done =>
    rintro _ rfl
    have hpow := lt_pow_rounds x.U
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, rfl⟩

/-! ## A round -/












private theorem Inv.loc_count {t : ℕ} {σ : State} (hI : Inv x μ fr t σ) : σ.loc Count = t := by
  obtain ⟨_, _, _, rfl, -⟩ := hI
  rfl






/-- It is an instance, once V stands at its place and the two matrices are still at theirs. -/
theorem pairsInst_pre (hpre : x.Pre μ fr) {t : ℕ} (ht : t < mpRounds x.U) {μ' : ℕ → ℤ}
    (sA : Seg μ' x.a x.A) (sB : Seg μ' x.b x.B) (sV : Seg μ' (fr + mpRounds x.U) (asked x t)) :
    (pairsInst x fr t).Pre μ' (fr + mpRounds x.U + x.n * x.n + x.n * x.n) :=
  have hA := hpre.belowA
  have hB := hpre.belowB
  have hU := hpre.U_pos
  have hle : ∀ L : List ℤ, AbsLe L x.U → AbsLe L (6 * x.U : ℕ) := fun L hL y hy =>
    (hL y hy).trans (by push_cast; omega)
  { n_pos := hpre.n_pos
    U_pos := by change 1 ≤ 6 * x.U; omega
    lenX := hpre.lenA
    lenY := hpre.lenB
    lenV := length_asked x t
    segX := sA
    segY := sB
    segV := sV
    leX := hle _ hpre.leA
    leY := hle _ hpre.leB
    leV := fun y hy => by
      obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
      exact (abs_asked_le hpre ht y' hy').trans (le_of_eq (by simp [pairsInst]))
    belowX := by simp only [pairsInst]; omega
    belowY := by simp only [pairsInst]; omega
    belowV := by simp only [pairsInst]; omega
    belowOut := by simp only [pairsInst]; omega
    apartX := by simp only [pairsInst]; omega
    apartY := by simp only [pairsInst]; omega
    apartV := by simp only [pairsInst]; omega }

/-- **One round** goes from the state with t + 1 remaining rounds to the state with t. -/
theorem round_spec (C : Ctx P₀ R₀ pPairs pFill pAddc pBump T r) (hpre : x.Pre μ fr)
    (hlim : Lim lim d r x fr) {t : ℕ} (ht : t < mpRounds x.U) {σ : State}
    (hI : Inv x μ fr (t + 1) σ) :
    Ends lim (P₀ ++ R₀) d (mpRound pPairs pAddc pBump) σ (roundTime T x.n x.U) (Inv x μ fr t) := by
  obtain ⟨power, unused, μ₀, rfl, hM⟩ := hI
  have hw := hlim.space
  have hlenLo := length_lows x (t + 1)
  ((obtain ⟨⟩ := id hlim); (obtain ⟨⟩ := id hpre); (obtain ⟨⟩ := id hM))
  unfold mpRound roundTime
  -- count := count - 1; power := mem[fr + count]
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen t ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (2 ^ t) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hM.pows t ht]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hM.pows t ht] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hM.pows t ht] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- addc(n², power, c, asked): V := lo + 2^t
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
            ((addc_meets C.addc (2 ^ t) (fr + mpRounds x.U) hM.lo
                (length_lows x _) (by omega) (by omega) fun y hy =>
                (abs_asked_le hpre ht y hy).trans (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (addc_meets C.addc (2 ^ t) (fr + mpRounds x.U) hM.lo (length_lows x _)
              (by omega) (by omega) fun y hy =>
              (abs_asked_le hpre ht y hy).trans (by omega))
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
              ⟨sV, sameAddc⟩
                  -- The solver writes its flags.
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- The solver writes its flags.
  refine Ends.callToThen (T' := T x.n (6 * x.U)) (C.sol.meets R₀ (pairsInst x fr t)
    (fr + mpRounds x.U + x.n * x.n + x.n * x.n) (pairsInst_pre hpre ht
      hpre.segA.keep hpre.segB.keep sV)
    ⟨hlim.solver, by simp only [pairsTask, pairsInst]; omega, hw,
      by simp only [pairsTask, pairsInst]; omega⟩) ?_ (by simp [pairsTask, pairsInst])
  rintro _ μ₂ ⟨sF, keptSolver⟩
  -- What the task promises, in terms of x: the flags, and no other change below the solver's free
  -- pointer.
  replace sF : Seg μ₂ (fr + mpRounds x.U + x.n * x.n) (flags x t) := sF
  replace keptSolver : KeptBut μ₁ μ₂ (fr + mpRounds x.U + x.n * x.n + x.n * x.n)
    (fr + mpRounds x.U + x.n * x.n) (x.n * x.n) := keptSolver
  -- bump(n², power, flags, c): lo grows by 2^t where the flag is 0
  have hpow := pow_range hpre.U_pos ht
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
            ((bump_meets C.bump (2 ^ t) sF hM.lo.keep
                ⟨length_flags x t, length_lows x _⟩ (by omega) (by omega)
                (flags_eq_zero_or_one x t) (absLe_lows hpre _)
                ⟨by (rw [abs_of_pos hpow.1]); (omega), by omega⟩)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (bump_meets C.bump (2 ^ t) sF hM.lo.keep
              ⟨length_flags x t, length_lows x _⟩ (by omega) (by omega)
              (flags_eq_zero_or_one x t) (absLe_lows hpre _)
              ⟨by (rw [abs_of_pos hpow.1]); (omega), by omega⟩)
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
        ((rintro _ μ₃ ⟨hnew, sameBump⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨_, _, μ₃, rfl,
    { lo := lows_round hpre t ▸ hnew
      pows := fun i hi => (by ((try refine Light.SameOn.cell ?_);
                                (intro apspMacro_154362_0 apspMacro_154362_1);
                                (first
                                  |
                                    ((((repeat
                                              (((with_reducible
                                                      rename Light.SameOn _ _ _ => apspMacro_154362_2));
                                                ((try
                                                      have :=
                                                        apspMacro_154362_2 apspMacro_154362_0 (by omega)));
                                                (revert apspMacro_154362_2)));
                                          (intros);
                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                      (omega))
                                  |
                                    ((simp [] at apspMacro_154362_1);
                                      (((repeat
                                              (((with_reducible
                                                      rename Light.SameOn _ _ _ => apspMacro_154362_3));
                                                ((try
                                                      have :=
                                                        apspMacro_154362_3 apspMacro_154362_0 (by omega)));
                                                (revert apspMacro_154362_3)));
                                          (intros);
                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                      (omega))
                                  |
                                    ((((repeat
                                              (((with_reducible
                                                      rename Light.SameOn _ _ _ => apspMacro_154362_4));
                                                ((try
                                                      have :=
                                                        apspMacro_154362_4 apspMacro_154362_0 (by omega)));
                                                (revert apspMacro_154362_4)));
                                          (intros);
                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                      (fail
                                          "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                    SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                    its condition K x does not follow from the hypotheses.")))) : μ₃ (fr + i) = μ₀ (fr + i)).trans (hM.pows i hi)
      kept := by ((try refine Light.SameOn.cell ?_);
                   (intro apspMacro_154446_0 apspMacro_154446_1);
                   (first
                     |
                       ((((repeat
                                 (((with_reducible
                                         rename Light.SameOn _ _ _ => apspMacro_154446_2));
                                   ((try
                                         have :=
                                           apspMacro_154446_2 apspMacro_154446_0 (by omega)));
                                   (revert apspMacro_154446_2)));
                             (intros);
                             (try simp only [Function.update_apply, Light.wrote] at *)));
                         (omega))
                     |
                       ((simp [] at apspMacro_154446_1);
                         (((repeat
                                 (((with_reducible
                                         rename Light.SameOn _ _ _ => apspMacro_154446_3));
                                   ((try
                                         have :=
                                           apspMacro_154446_3 apspMacro_154446_0 (by omega)));
                                   (revert apspMacro_154446_3)));
                             (intros);
                             (try simp only [Function.update_apply, Light.wrote] at *)));
                         (omega))
                     |
                       ((((repeat
                                 (((with_reducible
                                         rename Light.SameOn _ _ _ => apspMacro_154446_4));
                                   ((try
                                         have :=
                                           apspMacro_154446_4 apspMacro_154446_0 (by omega)));
                                   (revert apspMacro_154446_4)));
                             (intros);
                             (try simp only [Function.update_apply, Light.wrote] at *)));
                         (fail
                             "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                       its condition K x does not follow from the hypotheses.")))) }⟩

/-- **The rounds** go from the state with R remaining rounds to the state with none. -/
theorem rounds_spec (C : Ctx P₀ R₀ pPairs pFill pAddc pBump T r) (hpre : x.Pre μ fr)
    (hlim : Lim lim d r x fr) {σ : State} (hI : Inv x μ fr (mpRounds x.U) σ) :
    Ends lim (P₀ ++ R₀) d (.while ((Light.Cond.lt (k 0) (v Count))) (mpRound pPairs pAddc pBump)) σ
      (mpRounds x.U * (roundTime T x.n x.U + 4) + 4) (Inv x μ fr 0) := by
  have hzero : ((0 : ℕ) : ℤ) ≤ lim.word := by have := hlim.word; omega
  refine Ends.whileConst (fun j σ => Inv x μ fr (mpRounds x.U - j) σ) (mpRounds x.U)
    (roundTime T x.n x.U) (by simpa using hI) ?round ?done
    (by simp only [Cond.cost, Expr.cost]; exact le_of_eq (by ring))
  case round =>
    intro j σ₂ hj hI₂
    obtain ⟨t, ht⟩ : ∃ t, mpRounds x.U - j = t + 1 := ⟨mpRounds x.U - j - 1, by omega⟩
    rw [show mpRounds x.U - (j + 1) = t by omega]
    rw [ht] at hI₂
    exact ⟨⟨hzero, trivial⟩, by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                                        Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                                        reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                                        Nat.cast_zero, Nat.cast_one, hI₂.loc_count]; omega,
      round_spec C hpre hlim (by omega) hI₂⟩
  case done =>
    intro σ₂ hI₂
    rw [Nat.sub_self] at hI₂
    exact ⟨⟨hzero, trivial⟩, by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                                        Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                                        reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                                        Nat.cast_zero, Nat.cast_one, hI₂.loc_count]; omega, hI₂⟩

end Mp

/-! ## The host -/

open Mp in
/-- **The host is correct**, in every program that begins with the solver's program and has the
three passes. -/
theorem mp_spec {P₀ R₀ : Program} {pPairs pFill pAddc pBump : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (C : Ctx P₀ R₀ pPairs pFill pAddc pBump T r) {lim : Limits} {d : ℕ}
    {x : MatInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr) (hok : (mpNeed r x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R₀) d (mpBody pPairs pFill pAddc pBump)
      ⟨frame (mpTask.args x ++ [(fr : ℤ)]), μ⟩ (mpTime T x.n x.U)
      fun σ' => mpTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hlim := lim_of_ok hok
  have hw := hlim.space
  have hcells := hlim.cells
  ((obtain ⟨⟩ := id hlim); (obtain ⟨⟩ := id hpre))
  have harea : 1 ≤ x.n * x.n := Nat.mul_pos hpre.n_pos hpre.n_pos
  -- For the comparisons of times below: of the steps counted for each round, 24 pay for its power
  -- of two.
  have hsplit : mpRounds x.U * (T x.n (6 * x.U) + 49 * (x.n * x.n) + 70) =
      mpRounds x.U * (roundTime T x.n x.U + 4) + 24 * mpRounds x.U := by unfold roundTime; ring
  unfold mpBody mpTime
  -- The numbers n², 2U, 4U, −2U, 6U, and the powers of two.
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (consts_spec hpre hlim) ?_ ?_
      | refine Light.Ends.pieceLast (consts_spec hpre hlim) ?_ ?_);
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
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (powers_spec hpre hlim) ?_ ?_
      | refine Light.Ends.pieceLast (powers_spec hpre hlim) ?_ ?_);
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
  -- asked := fr + R; flags := asked + n²; solverFree := flags + n²
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (fr + mpRounds x.U : ℕ) ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen (fr + mpRounds x.U + x.n * x.n : ℕ) ?_ ?_ ?_);
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
          (fr + mpRounds x.U + x.n * x.n + x.n * x.n : ℕ)
            -- fill(c, n², −2U): the first lower bounds
            
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
  -- fill(c, n², −2U): the first lower bounds
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
            ((fill_meets C.fill (dst := x.c) (n := x.n * x.n) (x :=
                -(2 * (x.U : ℤ))) hw (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (fill_meets C.fill (dst := x.c) (n := x.n * x.n) (x :=
              -(2 * (x.U : ℤ))) hw (by omega))
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
              ⟨sLo, sameFill⟩
                  -- The rounds.
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- The rounds.
  refine (rounds_spec C hpre hlim ⟨_, _, μ₁, rfl,
    { lo := lows_top hpre ▸ sLo
      pows := fun i hi => (sameFill _ (by omega)).trans (wrote_done hi)
      kept := by ((try refine Light.SameOn.cell ?_);
                   (intro apspMacro_157575_0 apspMacro_157575_1);
                   (first
                     |
                       ((((repeat
                                 (((with_reducible
                                         rename Light.SameOn _ _ _ => apspMacro_157575_2));
                                   ((try
                                         have :=
                                           apspMacro_157575_2 apspMacro_157575_0 (by omega)));
                                   (revert apspMacro_157575_2)));
                             (intros);
                             (try simp only [Function.update_apply, Light.wrote] at *)));
                         (omega))
                     |
                       ((simp [] at apspMacro_157575_1);
                         (((repeat
                                 (((with_reducible
                                         rename Light.SameOn _ _ _ => apspMacro_157575_3));
                                   ((try
                                         have :=
                                           apspMacro_157575_3 apspMacro_157575_0 (by omega)));
                                   (revert apspMacro_157575_3)));
                             (intros);
                             (try simp only [Function.update_apply, Light.wrote] at *)));
                         (omega))
                     |
                       ((((repeat
                                 (((with_reducible
                                         rename Light.SameOn _ _ _ => apspMacro_157575_4));
                                   ((try
                                         have :=
                                           apspMacro_157575_4 apspMacro_157575_0 (by omega)));
                                   (revert apspMacro_157575_4)));
                             (intros);
                             (try simp only [Function.update_apply, Light.wrote] at *)));
                         (fail
                             "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                       its condition K x does not follow from the hypotheses.")))) }⟩).mono ?_ ?_
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
  · rintro _ ⟨_, _, μ', rfl, hM⟩
    exact ⟨lows_zero hpre ▸ hM.lo, hM.kept⟩

/-- The need of the host is polynomially bounded if the need of the solver is. -/
theorem polyNeed_mpNeed {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (mpNeed r) := by
  unfold mpNeed mpRounds
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

/-- **The (min,+)-product from "all pairs"**, as a host. -/
theorem isHost_mp : IsHost pairsTask mpTask mpTime mpNeed := by
  refine ⟨fun P p T r hs => ?_, fun r hr => polyNeed_mpNeed hr⟩
  refine ⟨[fillBody, addcBody, bumpBody, mpBody p P.length (P.length + 1) (P.length + 2)],
    P.length + 3, mpBody p P.length (P.length + 1) (P.length + 2), by simp,
    fun R lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact mp_spec ⟨hs, by simp, by simp, by simp⟩ hpre hok

end Light.Sec3

end
end

section


/-!
# Finding a negative triangle by halving

[VW18, Lemma 4.1], one of the reductions behind Theorem 21(b): an algorithm that
decides whether a graph has a negative triangle also finds one.  The search keeps three offsets and
a side length `h` such that the `h × h × h` sub-instance at these offsets has a negative triangle
(`NegAt`), and replaces `h` by `⌈h/2⌉`.

* The sub-instance is an instance of its own, made of three blocks of the matrices (`subMat`,
  `hasNegativeTriangle_subMat_iff`), so the decision algorithm can be asked about it.
* Each of the three ranges `[o, o + h)` is covered by its two halves `[o, o + ⌈h/2⌉)` and
  `[o + h - ⌈h/2⌉, o + h)`, which overlap in one place if `h` is odd.  So one of the eight triples
  of halves (`octants`) has a negative triangle (`NegAt.split`).
* At side length 1 the sub-instance is the triangle (`NegAt.triangle`).
* The side lengths `⌈n/2⌉, ⌈⌈n/2⌉/2⌉, …, 1` that the search goes through (`halvingChain`) add up to
  at most `2n` (`sum_halvingChain_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Sub-instances -/








/-- A negative triangle of an instance read from three lists, with the vertices as numbers. -/
private theorem hasNegativeTriangle_triOf_iff (h : ℕ) (AB BC AC : List ℤ) :
    (triOf h AB BC AC).HasNegativeTriangle ↔ ∃ a < h, ∃ b < h, ∃ c < h,
      entry h AB a b + entry h BC b c + entry h AC a c < 0 :=
  ⟨fun ⟨a, b, c, hS⟩ => ⟨a, a.2, b, b.2, c, c.2, hS⟩,
    fun ⟨a, ha, b, hb, c, hc, hS⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, hS⟩⟩

/-- The instance made of the three blocks has a negative triangle if and only if the sub-instance
has one. -/
theorem hasNegativeTriangle_subMat_iff (n : ℕ) (AB BC AC : List ℤ) (a0 b0 c0 h : ℕ) :
    (triOf h (subMat n h a0 b0 AB) (subMat n h b0 c0 BC)
      (subMat n h a0 c0 AC)).HasNegativeTriangle ↔ NegAt n AB BC AC a0 b0 c0 h := by
  rw [hasNegativeTriangle_triOf_iff, NegAt]
  constructor <;> rintro ⟨a, ha, b, hb, c, hc, hS⟩ <;> refine ⟨a, ha, b, hb, c, hc, ?_⟩ <;>
    simpa only [entry_subMat ha hb, entry_subMat hb hc, entry_subMat ha hc] using hS

/-- The whole instance is the sub-instance at the offsets 0 with side `n`. -/
theorem hasNegativeTriangle_iff_negAt (n : ℕ) (AB BC AC : List ℤ) :
    (triOf n AB BC AC).HasNegativeTriangle ↔ NegAt n AB BC AC 0 0 0 n := by
  simp only [hasNegativeTriangle_triOf_iff, NegAt, Nat.zero_add]

/-- A sub-instance of side 1 that has a negative triangle is a negative triangle. -/
theorem NegAt.triangle {n : ℕ} {AB BC AC : List ℤ} {a0 b0 c0 : ℕ}
    (h : NegAt n AB BC AC a0 b0 c0 1) (ha : a0 < n) (hb : b0 < n) (hc : c0 < n) :
    (triOf n AB BC AC).S ⟨a0, ha⟩ ⟨b0, hb⟩ ⟨c0, hc⟩ < 0 := by
  obtain ⟨a, ha', b, hb', c, hc', hS⟩ := h
  obtain rfl : a = 0 := by omega
  obtain rfl : b = 0 := by omega
  obtain rfl : c = 0 := by omega
  simpa only [TriangleInstance.S, triOf, Nat.add_zero] using hS

/-! ## The step of the search -/






/-- The entries of an octant are 0 or 1. -/
theorem le_one_of_mem_octants {t : ℕ × ℕ × ℕ} (ht : t ∈ octants) :
    t.1 ≤ 1 ∧ t.2.1 ≤ 1 ∧ t.2.2 ≤ 1 := by
  simp only [octants, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- A number below `h` lies in the lower or in the upper half of `[0, h)`. -/
private theorem exists_half {h h' a : ℕ} (ha : a < h) (hle : h' ≤ h) (hhalf : h ≤ 2 * h') :
    ∃ x a', (x = 0 ∨ x = 1) ∧ a' < h' ∧ a = x * (h - h') + a' := by
  by_cases hlow : a < h'
  · exact ⟨0, a, Or.inl rfl, hlow, by simp⟩
  · exact ⟨1, a - (h - h'), Or.inr rfl, by omega, by omega⟩

/-- **The step of the search.**  If the sub-instance of side `h` has a negative triangle and
`h/2 ≤ h' ≤ h`, then so has one of the eight sub-instances of side `h'` made of lower and upper
halves. -/
theorem NegAt.split {n : ℕ} {AB BC AC : List ℤ} {a0 b0 c0 h h' : ℕ}
    (hn : NegAt n AB BC AC a0 b0 c0 h) (hle : h' ≤ h) (hhalf : h ≤ 2 * h') :
    ∃ t ∈ octants, NegAt n AB BC AC (a0 + t.1 * (h - h')) (b0 + t.2.1 * (h - h'))
      (c0 + t.2.2 * (h - h')) h' := by
  obtain ⟨a, ha, b, hb, c, hc, hS⟩ := hn
  obtain ⟨x, a', hx, ha', rfl⟩ := exists_half ha hle hhalf
  obtain ⟨y, b', hy, hb', rfl⟩ := exists_half hb hle hhalf
  obtain ⟨z, c', hz, hc', rfl⟩ := exists_half hc hle hhalf
  refine ⟨(x, y, z), ?_, a', ha', b', hb', c', hc', ?_⟩
  · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
      simp [octants]
  · simpa only [Nat.add_assoc] using hS

/-! ## The chain of side lengths -/








/-- The chain is empty for `n ≤ 1`. -/
theorem halvingChain_of_lt {n : ℕ} (h : n < 2) : halvingChain n = [] := by
  rw [halvingChain, if_neg (by omega)]

/-- The chain starts with `⌈n/2⌉` for `n ≥ 2`. -/
theorem halvingChain_of_le {n : ℕ} (h : 2 ≤ n) :
    halvingChain n = (n + 1) / 2 :: halvingChain ((n + 1) / 2) := by
  rw [halvingChain, if_pos h]

/-- Every side length of the chain is at least 1 and smaller than `n`. -/
theorem bounds_of_mem_halvingChain {n h : ℕ} (hh : h ∈ halvingChain n) : 1 ≤ h ∧ h < n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : 2 ≤ n
    · rw [halvingChain_of_le hn, List.mem_cons] at hh
      rcases hh with rfl | hh
      · omega
      · have := ih _ (by omega) hh
        omega
    · rw [halvingChain_of_lt (by omega)] at hh
      exact absurd hh List.not_mem_nil

/-- The side lengths of the chain add up to at most `2n` (to at most `2n - 2`, for `n ≥ 1`). -/
theorem sum_halvingChain_le (n : ℕ) : (halvingChain n).sum ≤ 2 * n := by
  suffices h : ∀ n, 1 ≤ n → (halvingChain n).sum + 2 ≤ 2 * n by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [halvingChain_of_lt]
    · exact (Nat.le_add_right _ 2).trans (h n hn)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1
    by_cases hn : 2 ≤ n
    · -- With `m = ⌈n/2⌉` the sum is `m` plus at most `2m - 2`, and `3m ≤ 2n` for `n ≥ 2`.
      have hrest := ih ((n + 1) / 2) (by omega) (by omega)
      rw [halvingChain_of_le hn, List.sum_cons]
      omega
    · rw [halvingChain_of_lt (by omega), List.sum_nil]
      omega

end ThreeSumApsp.Spec

end
end

section


/-!
# Finding a negative triangle with an algorithm that decides whether there is one

[VW18, Lemma 4.1], a step of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).
The host asks the solver of Negative Triangle about the whole instance.  If the answer is yes, it
keeps three offsets and a side length h such that the h × h × h sub-instance at these offsets has a
negative triangle.  While h > 1 it puts h' = ⌈h/2⌉, asks about the eight sub-instances of side h'
made of the lower half [o, o + h') or the upper half [o + h - h', o + h) of each of the three
ranges, and goes on with one for which the answer is yes.  All eight questions are asked, and the
last yes counts.

The result is isHost_find : IsHost ntTask findTask findTime findNeed.  The proof goes from the
inside to the outside: one question (probe_meets: three calls of subCopy, one of the solver); the
questions of a round (try_spec and tries_spec, with the invariant TryInv); a round (round_spec; that
one of the eight answers is yes is NegAt.split); the rounds (loop_spec, with the invariant LoopInv);
the search and the host (search_spec, find_spec).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedures -/

namespace Probe
















end Probe













namespace Find























end Find




















































/-! ## Time and need -/





























namespace Find

variable {P₀ R : Program} {p pProbe pSub pCopy : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}

/-! ## The surroundings -/










/-- What find needs covers what the solver needs at a size h ≤ n, behind three blocks and up to
three levels further down. -/
theorem ok_sub {n U fr h : ℕ} (hok : (findNeed r n U).Ok lim fr d) (hh : h ≤ n) {fr' d' : ℕ}
    (hfr : fr' ≤ fr + 3 * (h * h)) (hd : d' ≤ d + 3) : (r h U).Ok lim fr' d' := by
  have hm : h ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hword := Finset.le_sup (f := fun h => (r h U).word) hm
  have hcells := Finset.le_sup (f := fun h => 3 * (h * h) + (r h U).cells) hm
  have hdepth := Finset.le_sup (f := fun h => (r h U).depth) hm
  refine hok.mono ?_ ?_ ?_ <;> simp only [findNeed] <;> omega

/-- What find needs covers the numbers up to n + 2 and three levels of calls. -/
private theorem word_depth_of_ok {n U fr : ℕ} (hok : (findNeed r n U).Ok lim fr d) :
    (n : ℤ) + 2 ≤ lim.word ∧ d + 3 ≤ lim.depth := by
  have hword := hok.word
  have hdepth := hok.depth
  simp only [findNeed] at hword hdepth
  omega

/-! ## One question -/







/-- The sub-instance is an instance, once its three blocks stand at their places. -/
theorem subInst_pre {x : TriInst} {μ μ' : ℕ → ℤ} {fr a0 b0 c0 h : ℕ} (hpre : x.Pre μ fr)
    (hh : 1 ≤ h) (sAB : Seg μ' fr (subMat x.n h a0 b0 x.AB))
    (sBC : Seg μ' (fr + h * h) (subMat x.n h b0 c0 x.BC))
    (sAC : Seg μ' (fr + h * h + h * h) (subMat x.n h a0 c0 x.AC)) :
    (subInst x fr a0 b0 c0 h).Pre μ' (fr + 3 * (h * h)) :=
  have hU : (0 : ℤ) ≤ (x.U : ℤ) := by positivity
  triPre_of_arrays hh hpre.U_pos
    { len := length_subMat .., seg := sAB, bound := abs_le_of_mem_subMat hU hpre.leAB }
    { len := length_subMat .., seg := sBC, bound := abs_le_of_mem_subMat hU hpre.leBC }
    { len := length_subMat .., bound := abs_le_of_mem_subMat hU hpre.leAC
      seg := (show fr + 2 * (h * h) = fr + h * h + h * h by omega) ▸ sAC }

/-- **probe** returns 1 if the sub-instance of side h at the offsets a0, b0, c0 has a negative
triangle, and 0 if not, and changes no cell below the free pointer. -/
theorem probe_meets (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ}
    (a0 b0 c0 h : ℕ) (hpre : x.Pre μ fr) (hh : 1 ≤ h)
    (hin : a0 + h ≤ x.n ∧ b0 + h ≤ x.n ∧ c0 + h ≤ x.n)
    (hok : (r h x.U).Ok lim (fr + 3 * (h * h)) (d + 1)) (hd : d + 1 < lim.depth) :
    Meets lim (P₀ ++ R) pProbe d [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, a0, b0, c0, h, fr] μ
      (probeTime T h x.U) fun res μ' =>
        res = flag (NegAt x.n x.AB x.BC x.AC a0 b0 c0 h) ∧ Kept μ μ' fr := by
  have hw := hok.space
  have hcells := hok.cells
  (obtain ⟨⟩ := id hpre)
  refine .of_body C.probe ?_
  unfold probeBody probeTime
  -- area := h * h
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
          (h * h : ℕ)
            -- subCopy(n, h, ab, a0, b0, fr)
            
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
  -- subCopy(n, h, ab, a0, b0, fr)
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
            ((subCopy_meets C.sub C.copy h a0 b0 fr hpre.segAB hpre.lenAB
                (by omega) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (subCopy_meets C.sub C.copy h a0 b0 fr hpre.segAB hpre.lenAB
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
              ⟨sAB, same₁⟩
                  -- subCopy(n, h, bc, b0, c0, fr + area)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- subCopy(n, h, bc, b0, c0, fr + area)
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
            ((subCopy_meets C.sub C.copy h b0 c0 (fr + h * h) hpre.segBC.keep
                hpre.lenBC (by omega) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (subCopy_meets C.sub C.copy h b0 c0 (fr + h * h) hpre.segBC.keep
              hpre.lenBC (by omega) (by omega))
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
              ⟨sBC, same₂⟩
                  -- subCopy(n, h, ac, a0, c0, fr + area + area)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- subCopy(n, h, ac, a0, c0, fr + area + area)
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
            ((subCopy_meets C.sub C.copy h a0 c0 (fr + h * h + h * h)
                hpre.segAC.keep hpre.lenAC (by omega) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (subCopy_meets C.sub C.copy h a0 c0 (fr + h * h + h * h)
              hpre.segAC.keep hpre.lenAC (by omega) (by omega))
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
              ⟨sAC, same₃⟩
                  -- The solver is asked about the three blocks.
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- The solver is asked about the three blocks.
  refine Ends.callTo (T' := T h x.U) (C.sol.meets R (subInst x fr a0 b0 c0 h) (fr + 3 * (h * h))
    (subInst_pre hpre hh sAB.keep sBC.keep sAC) hok) ?_ (by (((try have := Light.Std.space_le (by assumption)));
                                                              ((try have := Light.Std.const_le (by assumption)));
                                                              (simp [Light.Limits.Addr, abs_le, -abs_mul, ntTask, subInst] <;> omega)))
  rintro _ μ₄ ⟨rfl, same₄⟩
  exact ⟨flag_congr (hasNegativeTriangle_subMat_iff ..), by ((try refine Light.SameOn.cell ?_);
                                                                (intro apspMacro_170187_0 apspMacro_170187_1);
                                                                (first
                                                                  |
                                                                    ((((repeat
                                                                              (((with_reducible
                                                                                      rename Light.SameOn _ _ _ => apspMacro_170187_2));
                                                                                ((try
                                                                                      have :=
                                                                                        apspMacro_170187_2 apspMacro_170187_0 (by omega)));
                                                                                (revert apspMacro_170187_2)));
                                                                          (intros);
                                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                      (omega))
                                                                  |
                                                                    ((simp [] at apspMacro_170187_1);
                                                                      (((repeat
                                                                              (((with_reducible
                                                                                      rename Light.SameOn _ _ _ => apspMacro_170187_3));
                                                                                ((try
                                                                                      have :=
                                                                                        apspMacro_170187_3 apspMacro_170187_0 (by omega)));
                                                                                (revert apspMacro_170187_3)));
                                                                          (intros);
                                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                      (omega))
                                                                  |
                                                                    ((((repeat
                                                                              (((with_reducible
                                                                                      rename Light.SameOn _ _ _ => apspMacro_170187_4));
                                                                                ((try
                                                                                      have :=
                                                                                        apspMacro_170187_4 apspMacro_170187_0 (by omega)));
                                                                                (revert apspMacro_170187_4)));
                                                                          (intros);
                                                                          (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                      (fail
                                                                          "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                    SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                    its condition K x does not follow from the hypotheses."))))⟩

/-! ## The questions of a round -/











private theorem TryInv.imp {x : FindInst} {μ : ℕ → ℤ} {fr a0 b0 c0 h h' : ℕ} {Done Done' : Prop}
    {σ : State} (H : TryInv x μ fr a0 b0 c0 h h' Done σ) (hD : Done' → Done) :
    TryInv x μ fr a0 b0 c0 h h' Done' σ := by
  obtain ⟨na, nb, nc, reply, μ', hσ, hk, hin, hneg⟩ := H
  exact ⟨na, nb, nc, reply, μ', hσ, hk, hin, fun hd => hneg (hD hd)⟩





/-- **One question** keeps the invariant, and notes the offsets of its sub-instance if the answer is
yes. -/
theorem try_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ : ℕ → ℤ}
    {fr a0 b0 c0 h h' : ℕ} (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d)
    (hh : 1 ≤ h' ∧ h' ≤ h) (hin : a0 + h ≤ x.n ∧ b0 + h ≤ x.n ∧ c0 + h ≤ x.n) {t : ℕ × ℕ × ℕ}
    (ht : t.1 ≤ 1 ∧ t.2.1 ≤ 1 ∧ t.2.2 ≤ 1) {Done : Prop} {σ : State}
    (hI : TryInv x μ fr a0 b0 c0 h h' Done σ) :
    Ends lim (P₀ ++ R) d (tryStmt pProbe t) σ (tryTime T h' x.U)
      (TryInv x μ fr a0 b0 c0 h h' (Done ∨ NegOct x a0 b0 c0 h h' t)) := by
  obtain ⟨na, nb, nc, reply, μ', rfl, hk, hcand, hneg⟩ := hI
  obtain ⟨t₁, t₂, t₃⟩ := t
  obtain ⟨hword, hdepth⟩ := word_depth_of_ok hok
  -- Each offset moves by 0 or by δ = h - h'.
  obtain ⟨ht₁, ht₂, ht₃⟩ : t₁ ≤ 1 ∧ t₂ ≤ 1 ∧ t₃ ≤ 1 := ht
  have hδ₁ : t₁ * (h - h') ≤ h - h' := by simpa using Nat.mul_le_mul_right (h - h') ht₁
  have hδ₂ : t₂ * (h - h') ≤ h - h' := by simpa using Nat.mul_le_mul_right (h - h') ht₂
  have hδ₃ : t₃ * (h - h') ≤ h - h' := by simpa using Nat.mul_le_mul_right (h - h') ht₃
  unfold tryStmt tryTime
  -- reply := probe(n, U, ab, bc, ac, a0 + t₁ δ, b0 + t₂ δ, c0 + t₃ δ, h', fr)
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
            ((probe_meets C (a0 + t₁ * (h - h')) (b0 + t₂ * (h - h'))
                (c0 + t₃ * (h - h')) h' hpre.toPre.keep hh.1 (by omega)
                (ok_sub hok (by omega) le_rfl (by omega)) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (probe_meets C (a0 + t₁ * (h - h')) (b0 + t₂ * (h - h'))
              (c0 + t₃ * (h - h')) h' hpre.toPre.keep hh.1 (by omega)
              (ok_sub hok (by omega) le_rfl (by omega)) (by omega))
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
        ((rintro _ μ''
              ⟨rfl, hk'⟩
                  -- if reply = 1
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- if reply = 1
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
  · -- na := a0 + t₁ δ; nb := b0 + t₂ δ; nc := c0 + t₃ δ
    refine Ends.setToThen (a0 + t₁ * (h - h') : ℕ) ?_
    refine Ends.setToThen (b0 + t₂ * (h - h') : ℕ) ?_
    refine Ends.setTo (c0 + t₃ * (h - h') : ℕ) ?_
    exact ⟨_, _, _, _, μ'', rfl, hk.trans hk', by omega,
      fun _ => flag_eq_one_iff.1 (by simpa using hyes)⟩
  · refine Ends.skip ⟨na, nb, nc, _, μ'', rfl, hk.trans hk', hcand, ?_⟩
    rintro (hD | hD)
    · exact hneg hD
    · exact absurd (by simpa [NegOct] using flag_of hD) hno

/-- The questions for a list of triples keep the invariant: afterwards na, nb, nc are the offsets of
a sub-instance with a negative triangle, if one of the triples stands for such a sub-instance. -/
theorem tries_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ : ℕ → ℤ}
    {fr a0 b0 c0 h h' : ℕ} (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d)
    (hh : 1 ≤ h' ∧ h' ≤ h) (hin : a0 + h ≤ x.n ∧ b0 + h ≤ x.n ∧ c0 + h ≤ x.n)
    (ts : List (ℕ × ℕ × ℕ)) (hts : ∀ t ∈ ts, t.1 ≤ 1 ∧ t.2.1 ≤ 1 ∧ t.2.2 ≤ 1) {Done : Prop}
    {σ : State} (hI : TryInv x μ fr a0 b0 c0 h h' Done σ) :
    Ends lim (P₀ ++ R) d (triesStmt pProbe ts) σ (ts.length * tryTime T h' x.U)
      (TryInv x μ fr a0 b0 c0 h h' (Done ∨ ∃ t ∈ ts, NegOct x a0 b0 c0 h h' t)) := by
  induction ts generalizing Done σ with
  | nil => exact Ends.skip (hI.imp (by simp))
  | cons t ts ih =>
    refine Ends.seq (tryTime T h' x.U) (ts.length * tryTime T h' x.U) ?_
      (by simp only [List.length_cons]; ring_nf; omega)
    refine (try_spec C hpre hok hh hin (hts t (by simp)) hI).mono le_rfl fun σ' hσ' => ?_
    refine (ih (fun t' ht' => hts t' (by simp [ht'])) hσ').mono le_rfl fun σ'' hσ'' => hσ''.imp ?_
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

/-! ## A round, and the search -/











private theorem LoopInv.loc_side {x : FindInst} {μ : ℕ → ℤ} {fr h : ℕ} {σ : State}
    (hI : LoopInv x μ fr h σ) : σ.loc Side = h := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl, -⟩ := hI
  rfl

/-- halfStmt puts ⌈h/2⌉ into h' and changes nothing else. -/
theorem half_spec {P : Program} {loc μ : ℕ → ℤ} {h : ℕ} (hside : loc Side = h)
    (hword : (h : ℤ) + 2 ≤ lim.word) :
    Ends lim P d halfStmt ⟨loc, μ⟩ (10 * ((h + 1) / 2) + 8) fun σ' =>
      σ' = ⟨Function.update loc Half ((h + 1) / 2 : ℕ), μ⟩ := by
  unfold halfStmt
  -- h' := 0
  refine Ends.setThen ?_
  -- while h' + h' < h: h' := h' + 1
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc Half j, μ⟩) ((h + 1) / 2) (by simp)
    ?round ?done
  case round =>
    rintro j _ hj rfl
    exact ⟨by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                  Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                  reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                  Nat.cast_zero, Nat.cast_one, Side, Half, hside, abs_le]; omega,
      by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
           Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
           reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
           Nat.cast_zero, Nat.cast_one, Side, Half, hside]; omega, by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                                                                        Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                                                                        reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                                                                        Nat.cast_zero, Nat.cast_one, Stmt.BlockSafe, abs_le]; omega,
      by simp⟩
  case done =>
    rintro _ rfl
    exact ⟨by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                  Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                  reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                  Nat.cast_zero, Nat.cast_one, Side, Half, hside, abs_le]; omega,
      by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
           Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
           reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
           Nat.cast_zero, Nat.cast_one, Side, Half, hside]; omega, rfl⟩




private theorem roundTime_le (T : ℕ → ℕ → ℕ) (h' U : ℕ) :
    roundTime T h' U + 4 ≤ roundBound T h' U := by
  have hsq : h' ≤ h' ^ 2 := Nat.le_self_pow (by norm_num) h'
  have hcopy : h' * (16 * h' + 31) = 16 * h' ^ 2 + 31 * h' := by ring
  unfold roundTime roundBound tryTime probeTime subCopyTime
  rw [hcopy]
  omega

/-- **One round** goes from a sub-instance of side h ≥ 2 with a negative triangle to one of side
⌈h/2⌉. -/
theorem round_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ : ℕ → ℤ} {fr h : ℕ}
    (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d) (hh : 2 ≤ h) {σ : State}
    (hI : LoopInv x μ fr h σ) :
    Ends lim (P₀ ++ R) d (roundStmt pProbe) σ (roundTime T ((h + 1) / 2) x.U)
      (LoopInv x μ fr ((h + 1) / 2)) := by
  obtain ⟨a0, b0, c0, z₁, z₂, z₃, z₄, z₅, z₆, μ', rfl, hk, hin, hneg⟩ := hI
  obtain ⟨hword, -⟩ := word_depth_of_ok hok
  unfold roundStmt roundTime
  -- h' := ⌈h/2⌉
  focus
    (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_);
    (first
      | refine Light.Ends.pieceThen (half_spec (h := h) rfl (by omega)) ?_ ?_
      | refine Light.Ends.pieceLast (half_spec (h := h) rfl (by omega)) ?_ ?_);
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
  rw [update_frame_setLocal]
  generalize hh' : (h + 1) / 2 = h'
  -- δ := h - h'
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
          (h - h' : ℕ)
            -- na := a0; nb := b0; nc := c0
            
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
  -- na := a0; nb := b0; nc := c0
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen a0 ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen b0 ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen c0 ?_ ?_ ?_);
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
  -- The eight questions: one of them has the answer yes.
  refine Ends.next (8 * tryTime T h' x.U) ((tries_spec C hpre hok (h := h) (h' := h')
    ⟨by omega, by omega⟩ hin octants (fun _ => le_one_of_mem_octants) (Done := False)
    ⟨a0, b0, c0, z₆, μ', rfl, hk, by omega, False.elim⟩).mono (by simp [octants]) ?_)
  rintro _ ⟨na, nb, nc, reply, μ'', rfl, hk', hcand, hneg'⟩
  -- a0 := na; b0 := nb; c0 := nc; h := h'
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen na ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen nb ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen nc ?_ ?_ ?_);
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
    (refine Light.Ends.setToThen h' ?_ ?_ ?_);
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
  exact ⟨na, nb, nc, _, _, _, _, _, _, μ'', rfl, hk', hcand,
    hneg' (.inr (hneg.split (by omega) (by omega)))⟩





/-- The rounds end with a sub-instance of side 1 that has a negative triangle. -/
theorem loop_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d) :
    ∀ (h : ℕ) (σ : State), 1 ≤ h → LoopInv x μ fr h σ →
      Ends lim (P₀ ++ R) d (.while ((Light.Cond.lt (k 1) (v Side))) (roundStmt pProbe)) σ (loopTime T h x.U)
        (LoopInv x μ fr 1) := by
  obtain ⟨hword, -⟩ := word_depth_of_ok hok
  have one : ((1 : ℕ) : ℤ) ≤ lim.word := by push_cast; omega
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro σ h1 hI
    by_cases hh : 2 ≤ h
    · -- One round, and then the rounds from ⌈h/2⌉ on.
      refine Ends.whileStep (roundTime T ((h + 1) / 2) x.U) (loopTime T ((h + 1) / 2) x.U)
        ⟨one, trivial⟩ (by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                                 Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                                 reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                                 Nat.cast_zero, Nat.cast_one, hI.loc_side]; omega)
        ((round_spec C hpre hok hh hI).mono le_rfl fun σ' hσ' => ih _ (by omega) σ' (by omega) hσ')
        ?_
      have := roundTime_le T ((h + 1) / 2) x.U
      simp only [loopTime, halvingChain_of_le hh, List.map_cons, List.sum_cons, Cond.cost,
        Expr.cost]
      omega
    · obtain rfl : h = 1 := by omega
      exact Ends.whileDone ⟨one, trivial⟩ (by simp only [Light.Expr.Safe, Light.Expr.val, Light.Expr.cost, Light.Op.eval,
                                                    Light.Cond.Holds, Light.Cond.cost, Light.Cond.Safe, Function.update_apply,
                                                    reduceIte, true_and, and_true, Nat.reduceEqDiff, Nat.cast_ofNat,
                                                    Nat.cast_zero, Nat.cast_one, hI.loc_side]; omega) hI
        (by simp [loopTime])

/-! ## The host -/

/-- **The search** finds a negative triangle if there is one. -/
theorem search_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ μ' : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d) (hk : Kept μ μ' fr)
    (hyes : (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle) (reply : ℤ) :
    Ends lim (P₀ ++ R) d (searchStmt pProbe)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.res, fr, 0, 0, 0, 0, 0, 0, 0, 0, 0, reply], μ'⟩
      (loopTime T x.n x.U + 23) fun σ' => findTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  obtain ⟨hword, -⟩ := word_depth_of_ok hok
  have hcells := hok.cells
  ((obtain ⟨⟩ := id hok); (obtain ⟨⟩ := id hpre))
  unfold searchStmt
  -- a0 := 0; b0 := 0; c0 := 0; h := n
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
    (refine Light.Ends.setToThen x.n ?_ ?_ ?_);
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
  -- The rounds.
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
            (loop_spec C hpre hok x.n _ hpre.n_pos
              ⟨0, 0, 0, _, _, _, _, _, _, μ', rfl, hk, by omega,
                (hasNegativeTriangle_iff_negAt ..).1 hyes⟩)
            ?_ ?_
      |
        refine
          Light.Ends.pieceLast
            (loop_spec C hpre hok x.n _ hpre.n_pos
              ⟨0, 0, 0, _, _, _, _, _, _, μ', rfl, hk, by omega,
                (hasNegativeTriangle_iff_negAt ..).1 hyes⟩)
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
    (on_goal -1 =>
        rintro _
          ⟨a0, b0, c0, z₁, z₂, z₃, z₄, z₅, z₆, μ'', rfl, hk', hin, hneg⟩
              -- res[0] := a0; res[1] := b0; res[2] := c0; the result is 1
              )
  -- res[0] := a0; res[1] := b0; res[2] := c0; the result is 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.storeToThen x.res a0 ?_ ?_ ?_);
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
    (refine Light.Ends.storeToThen (x.res + 1) b0 ?_ ?_ ?_);
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
    (refine Light.Ends.storeToThen (x.res + 2) c0 ?_ ?_ ?_);
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
  refine ⟨(flag_of hyes).symm, fun _ => ⟨⟨a0, by omega⟩, ⟨b0, by omega⟩, ⟨c0, by omega⟩, ?_, ?_, ?_,
    hneg.triangle ..⟩, by ((try refine Light.SameOn.cell ?_);
                              (intro apspMacro_179961_0 apspMacro_179961_1);
                              (first
                                |
                                  ((((repeat
                                            (((with_reducible
                                                    rename Light.SameOn _ _ _ => apspMacro_179961_2));
                                              ((try
                                                    have :=
                                                      apspMacro_179961_2 apspMacro_179961_0 (by omega)));
                                              (revert apspMacro_179961_2)));
                                        (intros);
                                        (try simp only [Function.update_apply, Light.wrote] at *)));
                                    (omega))
                                |
                                  ((simp [] at apspMacro_179961_1);
                                    (((repeat
                                            (((with_reducible
                                                    rename Light.SameOn _ _ _ => apspMacro_179961_3));
                                              ((try
                                                    have :=
                                                      apspMacro_179961_3 apspMacro_179961_0 (by omega)));
                                              (revert apspMacro_179961_3)));
                                        (intros);
                                        (try simp only [Function.update_apply, Light.wrote] at *)));
                                    (omega))
                                |
                                  ((((repeat
                                            (((with_reducible
                                                    rename Light.SameOn _ _ _ => apspMacro_179961_4));
                                              ((try
                                                    have :=
                                                      apspMacro_179961_4 apspMacro_179961_0 (by omega)));
                                              (revert apspMacro_179961_4)));
                                        (intros);
                                        (try simp only [Function.update_apply, Light.wrote] at *)));
                                    (fail
                                        "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                  SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                  its condition K x does not follow from the hypotheses."))))⟩
  · simp
  · simp
  · simp

/-- **find** returns 1 and writes a negative triangle to the cells from `res` if there is one, and
returns 0 if there is none (`findTask`), within `findTime` steps. -/
theorem find_spec (C : Ctx P₀ R p pProbe pSub pCopy T r) {x : FindInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (findNeed r x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (findBody p pProbe) ⟨frame (findTask.args x ++ [(fr : ℤ)]), μ⟩
      (findTime T x.n x.U) fun σ' => findTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  obtain ⟨hword, hdepth⟩ := word_depth_of_ok hok
  change Ends _ _ _ _ ⟨frame [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, x.res, fr], μ⟩ _ _
  unfold findBody findTime
  -- reply := solver(n, U, ab, bc, ac, fr)
  refine Ends.callToThen (T' := T x.n x.U) (C.sol.meets R x.toTriInst fr hpre.toPre
    (ok_sub hok le_rfl (by omega) (by omega))) ?_ (by simp [ntTask])
  rintro _ μ₀ ⟨rfl, hk⟩
  -- if reply = 0
  refine Ends.iteLast (fun hno => ?_) (fun hyes => ?_)
  · -- There is no negative triangle: the result is 0.
    refine Ends.setTo 0 ⟨?_, fun h01 => absurd h01 (by norm_num), by ((try refine Light.SameOn.cell ?_);
                                                                         (intro apspMacro_181126_0 apspMacro_181126_1);
                                                                         (first
                                                                           |
                                                                             ((((repeat
                                                                                       (((with_reducible
                                                                                               rename Light.SameOn _ _ _ => apspMacro_181126_2));
                                                                                         ((try
                                                                                               have :=
                                                                                                 apspMacro_181126_2 apspMacro_181126_0 (by omega)));
                                                                                         (revert apspMacro_181126_2)));
                                                                                   (intros);
                                                                                   (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                               (omega))
                                                                           |
                                                                             ((simp [] at apspMacro_181126_1);
                                                                               (((repeat
                                                                                       (((with_reducible
                                                                                               rename Light.SameOn _ _ _ => apspMacro_181126_3));
                                                                                         ((try
                                                                                               have :=
                                                                                                 apspMacro_181126_3 apspMacro_181126_0 (by omega)));
                                                                                         (revert apspMacro_181126_3)));
                                                                                   (intros);
                                                                                   (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                               (omega))
                                                                           |
                                                                             ((((repeat
                                                                                       (((with_reducible
                                                                                               rename Light.SameOn _ _ _ => apspMacro_181126_4));
                                                                                         ((try
                                                                                               have :=
                                                                                                 apspMacro_181126_4 apspMacro_181126_0 (by omega)));
                                                                                         (revert apspMacro_181126_4)));
                                                                                   (intros);
                                                                                   (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                               (fail
                                                                                   "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                             SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                             its condition K x does not follow from the hypotheses."))))⟩
    simpa using hno.symm
  · -- There is one: the search finds it.
    refine (search_spec C hpre hok hk (by_contra fun hcon => hyes ?_) _).mono ?_ fun _ h => h
    · simpa using flag_of_not hcon
    · simp only [loopTime]
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

/-! ## The need -/

/-- The need of find is polynomially bounded if the need of the solver is. -/
theorem polyNeed_find (hr : PolyNeed r) : PolyNeed (findNeed r) := by
  obtain ⟨s, e, hse⟩ := hr
  have hpoly := PolyBounded.polyBound PolyBounded.fst PolyBounded.snd s e
  have hle : ∀ {n h : ℕ}, h ∈ Finset.range (n + 1) → h ≤ n := fun hh =>
    Nat.le_of_lt_succ (Finset.mem_range.1 hh)
  refine PolyBounded.polyNeed ?_ ?_ ?_
  · refine PolyBounded.of_le (G := fun n U => n + 2 + _) (by first
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
                                                                          | apply hpoly
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
                                                                                        | apply hpoly
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
                                                                                  | apply hpoly
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
                                                                          | apply hpoly
                                                                          | apply ThreeSumApsp.Scale.SoftO.add
                                                                          | apply ThreeSumApsp.Scale.SoftO.mul
                                                                          | apply ThreeSumApsp.Scale.SoftO.pow
                                                                          | apply ThreeSumApsp.Scale.SoftO.max
                                                                          | apply ThreeSumApsp.Scale.SoftO.sub
                                                                          | apply ThreeSumApsp.Scale.SoftO.div))) fun n U =>
      Nat.add_le_add_left
        (Finset.sup_le fun h hh => (hse h U).1.trans (polyBound_cons_le (hle hh) ..)) _
  · refine PolyBounded.of_le (G := fun n U => 3 * (n * n) + _) (by first
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
                                                                                | apply hpoly
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
                                                                                              | apply hpoly
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
                                                                                        | apply hpoly
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
                                                                                | apply hpoly
                                                                                | apply ThreeSumApsp.Scale.SoftO.add
                                                                                | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                | apply ThreeSumApsp.Scale.SoftO.max
                                                                                | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                | apply ThreeSumApsp.Scale.SoftO.div))) fun n U =>
      Finset.sup_le fun h hh => Nat.add_le_add
        (Nat.mul_le_mul_left 3 (Nat.mul_le_mul (hle hh) (hle hh)))
        ((hse h U).2.1.trans (polyBound_cons_le (hle hh) ..))
  · refine PolyBounded.of_le (G := fun n U => 3 + _) (by first
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
                                                                      | apply hpoly
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
                                                                                    | apply hpoly
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
                                                                              | apply hpoly
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
                                                                      | apply hpoly
                                                                      | apply ThreeSumApsp.Scale.SoftO.add
                                                                      | apply ThreeSumApsp.Scale.SoftO.mul
                                                                      | apply ThreeSumApsp.Scale.SoftO.pow
                                                                      | apply ThreeSumApsp.Scale.SoftO.max
                                                                      | apply ThreeSumApsp.Scale.SoftO.sub
                                                                      | apply ThreeSumApsp.Scale.SoftO.div))) fun n U =>
      Nat.add_le_add_left
        (Finset.sup_le fun h hh => (hse h U).2.2.trans (polyBound_cons_le (hle hh) ..)) _

end Find

open Find

/-- **[VW18, Lemma 4.1]: finding a negative triangle from deciding whether there is one.** -/
theorem isHost_find : IsHost ntTask findTask findTime findNeed := by
  refine ⟨fun P p T r hsol => ⟨findProcs P.length p, P.length + 3, ?_⟩,
    fun r hr => polyNeed_find hr⟩
  refine ⟨findBody p (P.length + 2), by simp [findProcs], fun R' lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  have C : Ctx P (findProcs P.length p ++ R') p (P.length + 2) (P.length + 1) P.length T r :=
    ⟨hsol, by simp [findProcs], by simp [findProcs], by simp [findProcs]⟩
  exact find_spec C hpre hok

end Light.Sec3

end
end

section


/-!
# The arithmetic behind the running-time claims of Section 3

Elementary inequalities that the deductions between running-time claims use silently.

* `⌈n^{1/3}⌉ ≥ 1` and `(log s + 1)^e ≥ 1`.
* Thin instances, `n ≥ D^18` (Theorem 5, Corollaries 15, 16 and 26): the overheads `n D`, `n² / √D`
  and `1` are at most `n² / D^a`, and so at most the bounds `n² log² D / D^{1/18}` and
  `n² / D^{0.063}`.
* The pieces into which Corollary 15 splits `W` have at most `n² / √D` query pairs (`splitCap_le`).
-/

public section

namespace ThreeSumApsp

/-! ## Two quantities that are at least 1 -/

/-- `⌈n^{1/3}⌉ ≥ 1` for `n ≥ 1`. -/
theorem one_le_cbrtCeil {n : ℕ} (hn : 1 ≤ n) : 1 ≤ cbrtCeil n :=
  Nat.ceil_pos.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) _)





/-! ## Thin instances: `n ≥ D^18` -/





























































/-! ## The pieces of Corollary 15 -/



































end ThreeSumApsp

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
# The (min,+)-product from Negative Triangle: the claim

[VW18, Theorem 4.2] in the form needed for Theorem 21(b).  The three hosts
(finding from deciding, all pairs from finding, the product from all pairs) are composed, and their
time functions are bounded with the two properties of a good running time: T(s)/s is nondecreasing,
and T(s) ≥ s² (1 + log u).

Each host has one bound, up to a constant factor: finding costs O(T(n)) (findTime_dominated: the
side lengths of the search add up to at most 2n, and T(h) ≤ (h/n) T(n)); all pairs cost
O(n² T(⌈n^{1/3}⌉)) (pairsTime_dominated: there are O(n²) rounds, rounds_le); the product costs
O(log u) calls (mpTime_dominated, mpRounds_le).  claim_VW18_Theorem_4_2 puts the three together.
-/

@[expose] public section

/-! ## Good running times -/

namespace ThreeSumApsp.GoodTime

variable {T : ℕ → ℝ → ℝ}

/-- A good running time is at least s². -/
theorem sq_le (hT : GoodTime T) {s : ℕ} (hs : 1 ≤ s) (u : ℝ) : (s : ℝ) ^ 2 ≤ T s u :=
  (le_mul_of_one_le_right (by positivity) (by linarith [logU_pos u])).trans (hT.1 s u hs)

/-- A good running time is at least 1. -/
theorem one_le (hT : GoodTime T) {s : ℕ} (hs : 1 ≤ s) (u : ℝ) : 1 ≤ T s u :=
  (one_le_pow₀ (Nat.one_le_cast.2 hs)).trans (hT.sq_le hs u)

/-- T(h) ≤ h T(s)/s for h ≤ s. -/
theorem le_mul_div (hT : GoodTime T) {h s : ℕ} (hh : 1 ≤ h) (hs : h ≤ s) (u : ℝ) :
    T h u ≤ (h : ℝ) * (T s u / s) := by
  have hdiv := hT.2 u h s hh hs
  rwa [div_le_iff₀ (by exact_mod_cast hh), mul_comm] at hdiv

/-- C T is a good running time for C ≥ 1. -/
theorem const_mul (hT : GoodTime T) {C : ℝ} (hC : 1 ≤ C) : GoodTime fun s u => C * T s u := by
  refine ⟨fun s u hs => (hT.1 s u hs).trans (le_mul_of_one_le_left ?_ hC), fun u s₁ s₂ h₁ h₂ => ?_⟩
  · linarith [hT.one_le hs u]
  · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hT.2 u s₁ s₂ h₁ h₂) (by linarith)

end ThreeSumApsp.GoodTime

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The least s with s³ ≥ n is ⌈n^{1/3}⌉. -/
theorem cbrtLeast_eq_cbrtCeil (n : ℕ) : cbrtLeast n = ThreeSumApsp.cbrtCeil n := by
  have key : ∀ s : ℕ, (n : ℝ) ^ (1 / 3 : ℝ) ≤ s ↔ n ≤ s ^ 3 := by
    intro s
    have h3 : ((s : ℝ) ^ 3) ^ (1 / 3 : ℝ) = s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    constructor
    · intro h
      have : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 ≤ (s : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) h 3
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at this
      norm_num at this
      exact_mod_cast this
    · intro h
      rw [← h3]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) (by norm_num)
  apply le_antisymm
  · exact cbrtLeast_le ((key _).1 (Nat.le_ceil _))
  · exact Nat.ceil_le.2 ((key _).2 (le_cbrtLeast_pow n))

namespace MinPlusFromNeg

/-! ## The parameters of a bound -/

























/-- The solver on the instance of the run keeps to its bound. -/
theorem Run.Valid.solver_le {p : Run} (hp : p.Valid) : (p.Tn p.n p.U : ℝ) ≤ p.T p.n p.u :=
  hp.solver _ _ _ hp.n_pos hp.U_pos hp.U_le

/-! ## Finding from deciding -/

/-- The round of the search that goes to the side length n costs O(T(n)):
8 (Tn + 150 n² + 130) ≤ 8 (T + 150 T + 130 T). -/
theorem roundBound_dominated :
    Dominated Run.Good (fun p => (roundBound p.Tn p.n p.U : ℝ)) fun p => p.T p.n p.u :=
  ((((Dominated.of_le fun p hp => hp.solver_le).add
    ((Dominated.of_le fun p hp => hp.good.sq_le hp.n_pos _).const_mul (c := 150) (by norm_num))).add
    (.const 130 fun p hp => hp.good.one_le hp.n_pos _)).const_mul (c := 8) (by norm_num)).congr
    (fun p _ => by simp [roundBound]) fun _ _ => rfl

/-- The rounds of the search cost O(T(n)): T(h) ≤ h (T(n)/n), and the side lengths add up to at most
2n. -/
theorem search_dominated :
    Dominated Run.Good (fun p => (((halvingChain p.n).map fun h => roundBound p.Tn h p.U).sum : ℕ))
      fun p => p.T p.n p.u := by
  obtain ⟨C, hC, hround⟩ := roundBound_dominated
  refine ⟨C * 2, by positivity, fun p hp => ?_⟩
  have hn : (0 : ℝ) < p.n := by exact_mod_cast hp.n_pos
  have hτ : 0 ≤ p.T p.n p.u := by linarith [hp.good.one_le hp.n_pos p.u]
  calc ((((halvingChain p.n).map fun h => roundBound p.Tn h p.U).sum : ℕ) : ℝ)
      = ((halvingChain p.n).map fun h => (roundBound p.Tn h p.U : ℝ)).sum := by
        rw [Nat.cast_list_sum, List.map_map]
        rfl
    _ ≤ ((halvingChain p.n).map fun h : ℕ => (h : ℝ) * (C * (p.T p.n p.u / p.n))).sum := by
        refine List.sum_le_sum fun h hh => ?_
        obtain ⟨hpos, hlt⟩ := bounds_of_mem_halvingChain hh
        calc (roundBound p.Tn h p.U : ℝ) ≤ C * p.T h p.u :=
              hround { p with n := h } { hp with n_pos := hpos }
          _ ≤ C * ((h : ℝ) * (p.T p.n p.u / p.n)) :=
              mul_le_mul_of_nonneg_left (hp.good.le_mul_div hpos hlt.le p.u) hC
          _ = (h : ℝ) * (C * (p.T p.n p.u / p.n)) := by ring
    _ = ((halvingChain p.n).sum : ℕ) * (C * (p.T p.n p.u / p.n)) := by
        rw [List.sum_map_mul_right, Nat.cast_list_sum]
    _ ≤ (2 * p.n : ℕ) * (C * (p.T p.n p.u / p.n)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast sum_halvingChain_le p.n) (by positivity)
    _ = C * 2 * p.T p.n p.u := by
        push_cast
        field_simp

/-- **Finding from deciding**: the time grows by a constant factor only. -/
theorem findTime_dominated :
    Dominated Run.Good (fun p => (findTime p.Tn p.n p.U : ℝ)) fun p => p.T p.n p.u := by
  refine (((Dominated.const 40 fun p hp => hp.good.one_le hp.n_pos _).add
    (.of_le fun p hp => hp.solver_le)).add search_dominated).congr (fun p _ => ?_) fun _ _ => rfl
  simp only [findTime]
  push_cast
  rfl

/-! ## All pairs from finding -/

/-- The number of rounds of "all pairs" is at most 9n². -/
theorem rounds_le {n : ℕ} (hn : 1 ≤ n) : blockCount n (cbrtLeast n) ^ 3 + n ^ 2 ≤ 9 * n ^ 2 := by
  have hcube : n ≤ cbrtLeast n ^ 3 := le_cbrtLeast_pow n
  have hblocks : blockCount n (cbrtLeast n) * cbrtLeast n ≤ 2 * n := by
    have := blockCount_mul_lt (n := n) (one_le_cbrtLeast hn)
    have := cbrtLeast_le_self n
    omega
  generalize cbrtLeast n = s at *
  generalize blockCount n s = p at *
  -- p³ n ≤ p³ s³ = (p s)³ ≤ (2n)³
  have hmul : p ^ 3 * n ≤ 8 * n ^ 2 * n :=
    calc p ^ 3 * n ≤ p ^ 3 * s ^ 3 := Nat.mul_le_mul_left _ hcube
      _ = (p * s) ^ 3 := by ring
      _ ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left hblocks 3
      _ = 8 * n ^ 2 * n := by ring
  have := Nat.le_of_mul_le_mul_right hmul hn
  omega

/-- **All pairs from finding**: O(n²) questions at the size ⌈n^{1/3}⌉. -/
theorem pairsTime_dominated :
    Dominated Run.Good (fun p => (pairsTime p.Tn p.n p.U : ℝ))
      fun p => (p.n : ℝ) ^ 2 * p.T (cbrtCeil p.n) (3 * p.u) := by
  have hs : ∀ p : Run, p.Good → 1 ≤ cbrtLeast p.n := fun p hp => one_le_cbrtLeast hp.n_pos
  -- powers of n and of T(s), where s = ⌈n^{1/3}⌉
  let s : Scale Run (Fin 2) := .ofBases Run.Good
    ![fun p => p.n, fun p => p.T (cbrtLeast p.n) (3 * p.u)] fun i p hp => by
      fin_cases i
      exacts [Nat.one_le_cast.2 hp.n_pos, hp.good.one_le (hs p hp) _]
  have hn : s.SoftO (fun p => p.n) _ := .of_le_base 0 fun _ _ => le_rfl
  -- One round costs O(T(s)).
  have hsq : s.SoftO (fun p => cbrtLeast p.n ^ 2) _ :=
    .of_le_base 1 fun p hp => by exact_mod_cast hp.good.sq_le (hs p hp) (3 * p.u)
  have hsolver : s.SoftO (fun p => p.Tn (cbrtLeast p.n) (2 * p.U + 1)) _ :=
    .of_le_base 1 fun p hp => hp.solver _ _ _ (hs p hp) (by omega) (by
      have hU : (1 : ℝ) ≤ p.U := by exact_mod_cast hp.U_pos
      push_cast
      linarith [hp.U_le])
  -- There are O(n²) rounds.
  have hrounds : s.SoftO (fun p => blockCount p.n (cbrtLeast p.n) ^ 3 + p.n ^ 2) ![2, 0] :=
    (by first
        |
          ((apply ThreeSumApsp.Scale.SoftO.mono);
            (·
                repeat'
                  with_reducible
                    first
                    | exact ThreeSumApsp.Scale.SoftO.const _
                    | apply hn
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
                                  | apply hn
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
                            | apply hn
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
                    | apply hn
                    | apply ThreeSumApsp.Scale.SoftO.add
                    | apply ThreeSumApsp.Scale.SoftO.mul
                    | apply ThreeSumApsp.Scale.SoftO.pow
                    | apply ThreeSumApsp.Scale.SoftO.max
                    | apply ThreeSumApsp.Scale.SoftO.sub
                    | apply ThreeSumApsp.Scale.SoftO.div)) : s.SoftO (fun p => 9 * p.n ^ 2) ![2, 0]).of_le fun p hp => rounds_le hp.n_pos
  have htime : s.SoftO (fun p => pairsTime p.Tn p.n p.U) ![2, 1] := by
    unfold pairsTime
    first
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply hrounds
                | apply hn
                | apply hsq
                | apply hsolver
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
                              | apply hrounds
                              | apply hn
                              | apply hsq
                              | apply hsolver
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
                        | apply hrounds
                        | apply hn
                        | apply hsq
                        | apply hsolver
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
                | apply hrounds
                | apply hn
                | apply hsq
                | apply hsolver
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div))
  refine (htime.dominated fun _ _ => rfl).congr (fun _ _ => rfl) fun p _ => ?_
  rw [← cbrtLeast_eq_cbrtCeil]
  simp [Scale.mon, s, Scale.ofBases, Fin.prod_univ_two]

/-! ## The product from all pairs -/

/-- The number of rounds of the search is O(log u). -/
theorem mpRounds_le {U : ℕ} (hU : 1 ≤ U) {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (mpRounds U : ℝ) ≤ 8 * logU u := by
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hhalf := Real.one_half_lt_log_two
  have hpow : 2 ^ Nat.log 2 (4 * U) ≤ 4 * U := Nat.pow_log_le_self 2 (by omega)
  -- ⌊log₂ 4U⌋ log 2 ≤ log 4U = 2 log 2 + log U
  have hlog : (Nat.log 2 (4 * U) : ℝ) * Real.log 2 ≤ Real.log (4 * U) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_four] at hlog
  have hUu : Real.log U ≤ logU u := (Real.log_le_log (by positivity) hu).trans
    (log_le_logU (by linarith))
  have h2u := log_two_le_logU u
  have hleft : (Nat.log 2 (4 * U) : ℝ) * (1 / 2) ≤ (Nat.log 2 (4 * U) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hhalf.le (Nat.cast_nonneg _)
  simp only [mpRounds]
  push_cast
  -- ⌊log₂ 4U⌋ / 2 ≤ 3 logU u, and 1 ≤ 2 logU u
  linarith

/-- **The product from all pairs**: O(log u) calls, if a call takes at least n² steps. -/
theorem mpTime_dominated :
    Dominated Run.Quadratic (fun p => (mpTime p.Tn p.n p.U : ℝ))
      fun p => p.T p.n (6 * p.u) * logU p.u := by
  -- powers of T(n) and of 2 log u, which is at least 1
  let s : Scale Run (Fin 2) := .ofBases Run.Quadratic
    ![fun p => p.T p.n (6 * p.u), fun p => 2 * logU p.u] fun i p hp => by
      fin_cases i
      · exact (one_le_pow₀ (Nat.one_le_cast.2 hp.n_pos)).trans (hp.sq_le _)
      · change 1 ≤ 2 * logU p.u
        linarith [log_two_le_logU p.u, Real.one_half_lt_log_two]
  -- A round, and the steps before the rounds, cost O(T(n)).
  have hsq : s.SoftO (fun p => p.n * p.n) _ :=
    .of_le_base 0 fun p hp => by exact_mod_cast (sq (p.n : ℝ)).ge.trans (hp.sq_le (6 * p.u))
  have hsolver : s.SoftO (fun p => p.Tn p.n (6 * p.U)) _ :=
    .of_le_base 0 fun p hp => hp.solver p.n (6 * p.U) (6 * p.u) hp.n_pos
      (by have := hp.U_pos; omega) (by push_cast; linarith [hp.U_le])
  have hrounds : s.SoftO (fun p => mpRounds p.U) _ :=
    .of_dominated_base 1 <| .of_le_const_mul (C := 4) (by norm_num) fun p hp => by
      change _ ≤ 4 * (2 * logU p.u)
      linarith [mpRounds_le hp.U_pos hp.U_le]
  have htime : s.SoftO (fun p => mpTime p.Tn p.n p.U) ![1, 1] := by
    unfold mpTime
    first
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply hsq
                | apply hsolver
                | apply hrounds
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
                              | apply hsq
                              | apply hsolver
                              | apply hrounds
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
                        | apply hsq
                        | apply hsolver
                        | apply hrounds
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
                | apply hsq
                | apply hsolver
                | apply hrounds
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div))
  refine (htime.dominated fun _ _ => rfl).trans (.of_le_const_mul (C := 2) (by norm_num)
    fun p _ => le_of_eq ?_)
  simp [Scale.mon, s, Scale.ofBases, Fin.prod_univ_two]
  ring

end MinPlusFromNeg

open MinPlusFromNeg in
/-- **[VW18, Theorem 4.2]: the (min,+)-product from Negative Triangle.** -/
theorem claim_VW18_Theorem_4_2_sourceProof : Claim.VW18_Theorem_4_2 lightModel := by
  obtain ⟨C₁, hC₁, hfind⟩ := findTime_dominated
  obtain ⟨C₂, hC₂, hpairs⟩ := pairsTime_dominated
  obtain ⟨C₃, hC₃, hmp⟩ := mpTime_dominated
  refine ⟨18, C₃ * ((C₂ + 1) * (C₁ + 1)), by norm_num, by positivity, fun T hT hneg => ?_⟩
  -- Finding, in time (C₁ + 1) T(n), which is a good running time again.
  have hgood := hT.const_mul (le_add_of_nonneg_left hC₁ : 1 ≤ C₁ + 1)
  have hone : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ (C₁ + 1) * T (cbrtCeil n) u := fun n u hn =>
    hgood.one_le (one_le_cbrtCeil hn) u
  have hfindSolved : SolvedIn findTask fun n u => (C₁ + 1) * T n u :=
    isHost_find.solvedIn hneg fun Tn hTn n U u hn hU hu =>
      (hfind ⟨T, Tn, n, U, u⟩ ⟨⟨hTn, hn, hU, hu⟩, hT⟩).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith [hT.one_le hn u]))
  -- All pairs.
  have hpairsSolved : SolvedIn pairsTask fun n u =>
      (C₂ + 1) * ((n : ℝ) ^ 2 * ((C₁ + 1) * T (cbrtCeil n) (3 * u))) :=
    isHost_pairs.solvedIn hfindSolved fun Tn hTn n U u hn hU hu =>
      (hpairs ⟨_, Tn, n, U, u⟩ ⟨⟨hTn, hn, hU, hu⟩, hgood⟩).trans (mul_le_mul_of_nonneg_right
        (by linarith) (mul_nonneg (by positivity) (by linarith [hone n (3 * u) hn])))
  -- The product: a call for all pairs takes at least n² steps.
  have hmpSolved : SolvedIn mpTask fun n u =>
      C₃ * ((C₂ + 1) * ((n : ℝ) ^ 2 * ((C₁ + 1) * T (cbrtCeil n) (3 * (6 * u)))) * logU u) := by
    refine isHost_mp.solvedIn hpairsSolved fun Tn hTn n U u hn hU hu =>
      hmp ⟨_, Tn, n, U, u⟩ ⟨⟨hTn, hn, hU, hu⟩, fun u' => ?_⟩
    calc (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * ((C₁ + 1) * T (cbrtCeil n) (3 * u')) :=
          le_mul_of_one_le_right (by positivity) (hone n _ hn)
      _ ≤ _ := le_mul_of_one_le_left
          (mul_nonneg (by positivity) (by linarith [hone n (3 * u') hn])) (by linarith)
  refine ⟨_, hmpSolved, fun n U _ _ => le_of_eq ?_⟩
  rw [show 3 * (6 * U) = 18 * U by ring]
  ring

end Light.Sec3

end
end


theorem solution : ThreeSumApsp.Claim.VW18_Theorem_4_2 Light.lightModel := by
  exact @Light.Sec3.claim_VW18_Theorem_4_2_sourceProof

#print axioms solution
