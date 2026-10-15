-- Prove2me | solution 1 for Light.merge_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:05:35.701724+00:00
-- url     : https://prove2.me/submissions/35c19a0b-8832-4299-b8f5-f82f859ddf6e

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_of_blockSafe
import Theorems.Thm_Light_Ends_while
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSumApsp
end ThreeSumApsp

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







theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩



















































/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h









































/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/




























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











/-- A branch whose test holds. -/
theorem Stmt.Runs.ite_pos {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : s.Runs lim σ R) (hc : c.Holds σ := by (((try have := Light.Std.space_le (by assumption)));
                                                   ((try have := Light.Std.const_le (by assumption)));
                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                          ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun _ => h.1, fun hn => absurd hc hn⟩, by simpa only [Stmt.after, if_pos hc] using h.2⟩

/-- A branch whose test fails. -/
theorem Stmt.Runs.ite_neg {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop}
    (h : t.Runs lim σ R) (hc : ¬ c.Holds σ := by (((try have := Light.Std.space_le (by assumption)));
                                                      ((try have := Light.Std.const_le (by assumption)));
                                                      (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                             ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                             (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun hp => absurd hp hc, fun _ => h.1⟩, by simpa only [Stmt.after, if_neg hc] using h.2⟩



















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




theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl


















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}














































/-! ## The tactics -/









































end Light

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















































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]
















/-- Writing outside a segment. -/
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩





theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl






/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc

























































































end Light

end
end

section


/-!
# Merging two segments

merge(a, na, b, nb, dst) writes the merge of the na cells from a and the nb cells from b to the na +
nb cells from dst, within `mergeTime (na + nb)` steps (`merge_meets`).  The model is `List.merge`:
the next output is the head of the first list unless the head of the second list is smaller.
Nothing is assumed about the order of the two lists.  Numbers are only compared and copied, so their
size does not matter.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Merge

/-! ## The pure side: one step of List.merge on the rests of two lists -/

variable {l r : List ℤ} {i j : ℕ}

theorem step_left (hi : i < l.length) (hj : j < r.length) (h : l[i] ≤ r[j]) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj, List.cons_merge_cons]
  simp [h]

theorem step_right (hi : i < l.length) (hj : j < r.length) (h : r[j] < l[i]) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj, List.cons_merge_cons]
  simp [not_le.2 h]

theorem step_left_end (hi : i < l.length) (hj : r.length ≤ j) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  rw [List.drop_eq_nil_of_le hj, List.merge_right, List.merge_right, List.drop_eq_getElem_cons hi]

theorem step_right_end (hi : l.length ≤ i) (hj : j < r.length) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  rw [List.drop_eq_nil_of_le hi, List.nil_merge, List.nil_merge, List.drop_eq_getElem_cons hj]

end Merge

/-! ## The program -/

namespace Merge











end Merge

























namespace Merge
























variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}

/-- dst[i + j] := a[i]; i := i + 1. -/
theorem takeLeft (C : Pre lim μ a b dst l r) {σ : State} (h : Inv μ a b dst l r i j σ)
    (hi : i < l.length)
    (hm : (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j)) :
    mergeTakeLeft.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by
  obtain ⟨μ', out, rfl, -, hj, same, hlen, seg, hout⟩ := h
  (obtain ⟨⟩ := id C)
  have hread : μ' (a + i) = l[i] := (same _ (by omega)).trans (C.segL.get hi)
  have haddr : ((dst : ℤ) + i + j).toNat = dst + out.length := by omega
  refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                 ((try have := Light.Std.const_le (by assumption)));
                 (simp [Light.Limits.Addr, abs_le, -abs_mul, mergeTakeLeft] <;> omega)), i + 1, j, by omega,
    Function.update μ' (dst + out.length) l[i], out ++ [l[i]], ?_, hi, hj,
    same.update ⟨by omega, by omega⟩ _,
    by simp only [List.length_append, List.length_singleton]; omega,
    seg.snoc _, by rw [← hout, hm]; simp⟩
  simp [mergeTakeLeft, update_frame_setLocal, haddr, hread]

/-- dst[i + j] := b[j]; j := j + 1. -/
theorem takeRight (C : Pre lim μ a b dst l r) {σ : State} (h : Inv μ a b dst l r i j σ)
    (hj : j < r.length)
    (hm : (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1))) :
    mergeTakeRight.Runs lim σ (Taken μ a b dst l r (i + j + 1)) := by
  obtain ⟨μ', out, rfl, hi, -, same, hlen, seg, hout⟩ := h
  (obtain ⟨⟩ := id C)
  have hread : μ' (b + j) = r[j] := (same _ (by omega)).trans (C.segR.get hj)
  have haddr : ((dst : ℤ) + i + j).toNat = dst + out.length := by omega
  refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                 ((try have := Light.Std.const_le (by assumption)));
                 (simp [Light.Limits.Addr, abs_le, -abs_mul, mergeTakeRight] <;> omega)), i, j + 1, by omega,
    Function.update μ' (dst + out.length) r[j], out ++ [r[j]], ?_, hi, hj,
    same.update ⟨by omega, by omega⟩ _,
    by simp only [List.length_append, List.length_singleton]; omega,
    seg.snoc _, by rw [← hout, hm]; simp⟩
  simp [mergeTakeRight, update_frame_setLocal, haddr, hread]




/-- **merge(a, na, b, nb, dst)** writes `List.merge` of the two lists to dst and changes nothing
else. -/
theorem _root_.Light.merge_meets_sourceProof {p : ℕ} (hp : P[p]? = some mergeBody)
    (C : Pre lim μ a b dst l r) :
    Meets lim P p d [a, l.length, b, r.length, dst] μ (mergeTime (l.length + r.length)) fun _ μ' =>
      Seg μ' dst (l.merge r) ∧ SameOutside μ μ' dst (l.length + r.length) := by
  (obtain ⟨⟩ := id C)
  refine .of_body hp ?_
  unfold mergeTime
  -- i := 0; j := 0
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
            -- while i + j < na + nb
            
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
  -- while i + j < na + nb
  refine Ends.whileBlock (Taken μ a b dst l r) (l.length + r.length) ?start ?round ?done
    (by simp [mergeTakeLeft, mergeTakeRight]; omega)
  case start =>
    exact ⟨0, 0, rfl, μ, [], rfl, Nat.zero_le _, Nat.zero_le _, .refl, rfl, Seg.nil, by simp⟩
  case done =>
    rintro _ ⟨i, j, hij, μ', out, rfl, hi, hj, same, hlen, seg, hout⟩
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)] at hout
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, by simpa [← hout] using seg, same⟩
  case round =>
    rintro _ σ ht ⟨i, j, rfl, hI⟩
    have left := takeLeft C hI
    have right := takeRight C hI
    obtain ⟨μ', out, rfl, hi, hj, same, -⟩ := hI
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, ?_⟩
    -- The next output is the head of the first list unless the head of the second list is smaller.
    by_cases c1 : i < l.length
    · refine .ite_pos ?_
      by_cases c2 : j < r.length
      · have hreadL : μ' (a + i) = l[i] := (same _ (by omega)).trans (C.segL.get c1)
        have hreadR : μ' (b + j) = r[j] := (same _ (by omega)).trans (C.segR.get c2)
        refine .ite_pos ?_
        by_cases c3 : r[j] < l[i]
        · exact .ite_pos (right c2 (step_right c1 c2 c3)) (by simpa [hreadL, hreadR] using c3)
        · exact .ite_neg (left c1 (step_left c1 c2 (not_lt.1 c3)))
            (by simpa [hreadL, hreadR] using c3)
      · exact .ite_neg (left c1 (step_left_end c1 (by omega)))
    · exact .ite_neg (right (by omega) (step_right_end (by omega) (by omega)))

end Merge

end Light

end
end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {μ : Nat → Int} {a b dst : Nat} {l r : List.{0} Int} {p : Nat},
  @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt Light.mergeBody) →
    Light.Merge.Pre lim μ a b dst l r →
      Light.Meets lim P p d
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int l))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int r))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int))))))
        μ
        (Light.mergeTime
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int l)
            (@List.length.{0} Int r)))
        fun (x : Int) (μ' : Nat → Int) =>
        And
          (Light.Seg μ' dst
            (@List.merge.{0} Int l r fun (a b : Int) =>
              @Decidable.decide (@LE.le.{0} Int Int.instLEInt a b) (a.decLe b)))
          (Light.SameOutside μ μ' dst
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int l)
              (@List.length.{0} Int r))) := by
  exact @Light.merge_meets_sourceProof

#print axioms solution
