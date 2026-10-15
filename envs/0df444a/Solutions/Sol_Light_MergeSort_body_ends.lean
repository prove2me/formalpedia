-- Prove2me | solution 1 for Light.MergeSort.body_ends
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:43:43.272788+00:00
-- url     : https://prove2.me/submissions/5a94a110-1445-4a06-9794-dcb90cbb0885

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
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_Light_MergeSort_clog_split
import Theorems.Thm_Light_half_meets
import Theorems.Thm_Light_merge_meets


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


















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}











/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]


























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























































theorem Seg.take (h : Seg μ a l) (k : ℕ) : Seg μ a (l.take k) := fun i hi => by
  have hi' : i < l.length := by simp at hi; omega
  rw [List.getElem_take, h i hi']

theorem Seg.drop (h : Seg μ a l) (k : ℕ) : Seg μ (a + k) (l.drop k) := fun i hi => by
  have hi' : k + i < l.length := by simp at hi; omega
  rw [List.getElem_drop, ← h _ hi', Nat.add_assoc]

/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

































































































































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
    ⟨fun i hi => wrote_done (f := fun i => μ (src + i)) hi, by ((try refine Light.SameOn.cell ?_); (intro apspMacro_23476_0 apspMacro_23476_1);
                                                                    (first
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_23476_2));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_23476_2 apspMacro_23476_0 (by omega)));
                                                                                    (revert apspMacro_23476_2)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((simp [] at apspMacro_23476_1);
                                                                          (((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_23476_3));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_23476_3 apspMacro_23476_0 (by omega)));
                                                                                    (revert apspMacro_23476_3)));
                                                                              (intros);
                                                                              (try simp only [Function.update_apply, Light.wrote] at *)));
                                                                          (omega))
                                                                      |
                                                                        ((((repeat
                                                                                  (((with_reducible
                                                                                          rename Light.SameOn _ _ _ => apspMacro_23476_4));
                                                                                    ((try
                                                                                          have :=
                                                                                            apspMacro_23476_4 apspMacro_23476_0 (by omega)));
                                                                                    (revert apspMacro_23476_4)));
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

















end Light

end
end

section


/-!
# Merge sort

sort(n, a, fr) sorts the n cells from a in place, in ascending order (`sort_meets`).  It is the
recursive merge sort: sort the first ⌈n/2⌉ cells, sort the rest, merge the two halves into the n
cells from the free pointer fr, and copy them back.  It calls half, merge and copy.

The proof is an induction on n.  `body_ends` treats the body of the procedure, given that the
procedure sorts the lists of half the length, and `join_ends` its last two calls; `sorted_merge`
says that what the four calls leave is a sorted permutation of the list.  The number of steps,
`sortTime n`, is of the order n log n (`clog_split`, `time_split`), and the calls are nested
⌈log₂ n⌉ + 1 deep.  Numbers are only compared and copied, so their size does not matter.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program}

namespace MergeSort









end MergeSort




















namespace MergeSort




























/-- The recursion for the number of steps. -/
theorem time_split {n : ℕ} (hn : 2 ≤ n) :
    61 * n + 70 + sortTime ((n + 1) / 2) + sortTime (n - (n + 1) / 2) ≤ sortTime n := by
  have := clog_split hn
  unfold sortTime
  omega







/-- A list of at most one number is sorted. -/
theorem sorted_refl {μ : ℕ → ℤ} {a fr : ℕ} {L : List ℤ} (hseg : Seg μ a L) (hL : L.length ≤ 1) :
    Sorted μ a fr L μ := by
  refine ⟨⟨L, hseg, .refl _, ?_⟩, .refl⟩
  match L, hL with
  | [], _ => exact .nil
  | [x], _ => exact List.pairwise_singleton _ _

/-- The two halves are sorted one after the other, merged into the cells from fr, and copied
back. -/
theorem sorted_merge {μ μ₁ μ₂ μ₃ μ₄ : ℕ → ℤ} {a fr h m : ℕ} {L S₁ S₂ : List ℤ} (hh : h ≤ L.length)
    (hP₁ : S₁.Perm (L.take h)) (hO₁ : S₁.Pairwise (· ≤ ·))
    (hk₁ : KeptBut μ μ₁ fr a (L.take h).length) (hP₂ : S₂.Perm (L.drop h))
    (hO₂ : S₂.Pairwise (· ≤ ·)) (hk₂ : KeptBut μ₁ μ₂ fr (a + h) (L.drop h).length)
    (hk₃ : SameOutside μ₂ μ₃ fr m) (hS₄ : Seg μ₄ a (S₁.merge S₂))
    (hk₄ : SameOutside μ₃ μ₄ a L.length) : Sorted μ a fr L μ₄ := by
  refine ⟨⟨S₁.merge S₂, hS₄, ?_, hO₁.merge hO₂⟩, fun c hc => ?_⟩
  · calc (S₁.merge S₂).Perm (S₁ ++ S₂) := List.merge_perm_append _
      _ |>.Perm (L.take h ++ L.drop h) := hP₁.append hP₂
      _ = L := List.take_append_drop h L
  · have hl₁ : (L.take h).length = h := by simp; omega
    have hl₂ : (L.drop h).length = L.length - h := by simp
    have := hc.2
    rw [hk₄ c hc.2, hk₃ c (Or.inl hc.1), hk₂ c ⟨hc.1, by omega⟩, hk₁ c ⟨hc.1, by omega⟩]

variable {pSort pHalf pMerge pCopy : ℕ}

/-- Two lists, one after the other in the memory, are merged into the cells from fr and copied
back. -/
theorem join_ends (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) {d a fr h n : ℕ} {r : ℤ} {S₁ S₂ : List ℤ} {μ : ℕ → ℤ}
    (hl₁ : S₁.length = h) (hl₂ : S₂.length = n - h) (hh : h ≤ n) (hn : 1 ≤ n) (hS₁ : Seg μ a S₁)
    (hS₂ : Seg μ (a + h) S₂) (haf : a + n ≤ fr) (hfr : fr + n ≤ lim.space) (hd : d < lim.depth) :
    Ends lim P d (sortJoin pMerge pCopy) ⟨frame [n, a, fr, h, r], μ⟩ (56 * n + 34) fun σ' =>
      ∃ μ' : ℕ → ℤ, SameOutside μ μ' fr n ∧ Seg σ'.mem a (S₁.merge S₂) ∧
        SameOutside μ' σ'.mem a n := by
  have hlm : (S₁.merge S₂).length = n := by rw [List.length_merge]; omega
  -- merge(a, h, a + h, n - h, fr)
  have hmerge := merge_meets (d := d + 1) C.merge (a := a) (b := a + h) (dst := fr) (l := S₁)
    (r := S₂) ⟨hw, hS₁, hS₂, by omega, by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩
  rw [hl₁, hl₂, show h + (n - h) = n by omega] at hmerge
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
      | refine Light.Ends.callToThen (hmerge _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hmerge ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
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
              ⟨hseg, hk₁⟩
                  -- copy(fr, a, n)
                  );
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  -- copy(fr, a, n)
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
            ((copy_meets C.copy (src := fr) (dst := a) (n := n) hw (by omega)
                (by omega) (by omega))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          Light.Ends.callToThen
            (copy_meets C.copy (src := fr) (dst := a) (n := n) hw (by omega)
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
        ((rintro _ μ₂ ⟨hcopy, hk₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact ⟨μ₁, hk₁, fun i hi => (hcopy i (by omega)).trans (hseg i hi), hk₂⟩

/-- The body of sort, given that the procedure sorts the lists of at most half the length, rounded
up. -/
theorem body_ends_sourceProof (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) {d a fr : ℕ} {L : List ℤ}
    {μ : ℕ → ℤ} (hseg : Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space)
    (hd : d < lim.depth)
    (ih : ∀ (a' : ℕ) (L' : List ℤ) (μ' : ℕ → ℤ), 1 < L.length → 2 * L'.length ≤ L.length + 1 →
      Seg μ' a' L' → a' + L'.length ≤ fr →
      Meets lim P pSort (d + 1) [L'.length, a', fr] μ' (sortTime L'.length) fun _ =>
        Sorted μ' a' fr L') :
    Ends lim P d (sortBody pSort pHalf pMerge pCopy) ⟨frame [L.length, a, fr], μ⟩
      (sortTime L.length) fun σ' => Sorted μ a fr L σ'.mem := by
  -- if 1 < n
  refine Ends.iteLast (fun hc => ?_) (fun hc => Ends.skip (sorted_refl hseg (by simpa using hc)))
    (hT := by simp [sortTime])
  have hn : 1 < L.length := by simpa using hc
  have htime := time_split hn
  have hhalf := half_meets (d := d + 1) C.half μ (h := L.length)
    (le_trans (by exact_mod_cast (by omega : L.length + 1 ≤ lim.space)) hw)
  have hlt : (L.length + 1) / 2 < L.length := by omega
  have hpos : 1 ≤ (L.length + 1) / 2 := by omega
  have htwice : 2 * ((L.length + 1) / 2) ≤ L.length + 1 := by omega
  have htwice' : L.length ≤ 2 * ((L.length + 1) / 2) := by omega
  generalize (L.length + 1) / 2 = h at *
  have hl₁ : (L.take h).length = h := by simp; omega
  have hl₂ : (L.drop h).length = L.length - h := by simp
  -- h := half(n)
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
      | refine Light.Ends.callToThen (hhalf _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hhalf ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
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
        ((rintro _ μ₀ ⟨rfl, hμ₀⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  obtain rfl : μ = μ₀ := hμ₀.symm
  -- sort(h, a, fr)
  have hsort₁ := ih a (L.take h) μ hn (by omega) (hseg.take h) (by omega)
  rw [hl₁] at hsort₁
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
      | refine Light.Ends.callToThen (hsort₁ _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hsort₁ ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
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
        ((rintro _ μ₁ ⟨⟨S₁, hS₁, hP₁, hO₁⟩, hk₁⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hseg₂ : Seg μ₁ (a + h) (L.drop h) :=
    (hseg.drop h).congr fun i hi => hk₁ _ ⟨by omega, Or.inr (by omega)⟩
  -- sort(n - h, a + h, fr)
  have hsort₂ := ih (a + h) (L.drop h) μ₁ hn (by omega) hseg₂ (by omega)
  rw [hl₂] at hsort₂
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
      | refine Light.Ends.callToThen (hsort₂ _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hsort₂ ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
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
        ((rintro _ μ₂ ⟨⟨S₂, hS₂, hP₂, hO₂⟩, hk₂⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hlS₁ := hP₁.length_eq
  have hS₁' : Seg μ₂ a S₁ := hS₁.congr fun i hi => hk₂ _ ⟨by omega, Or.inl (by omega)⟩
  -- merge and copy
  refine (join_ends C hw (hP₁.length_eq.trans hl₁) (hP₂.length_eq.trans hl₂) hlt.le hn.le hS₁' hS₂
    haf hfr hd).mono (by first
                         |
                           ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
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
  rintro _ ⟨μ₃, hk₃, hS₄, hk₄⟩
  exact sorted_merge hlt.le hP₁ hO₁ hk₁ hP₂ hO₂ hk₂ hk₃ hS₄ hk₄





















end MergeSort

end Light

end
end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {pSort pHalf pMerge pCopy : Nat},
  Light.MergeSort.Procs P pSort pHalf pMerge pCopy →
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
      @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word →
        ∀ {d a fr : Nat} {L : List.{0} Int} {μ : Nat → Int},
          Light.Seg μ a L →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a (@List.length.{0} Int L)) fr →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) fr (@List.length.{0} Int L))
                  lim.space →
                @LT.lt.{0} Nat instLTNat d lim.depth →
                  (∀ (a' : Nat) (L' : List.{0} Int) (μ' : Nat → Int),
                      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@List.length.{0} Int L) →
                        @LE.le.{0} Nat instLENat
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int L'))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int L)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          Light.Seg μ' a' L' →
                            @LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a'
                                  (@List.length.{0} Int L'))
                                fr →
                              Light.Meets lim P pSort
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int L'))
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a')
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr) (@List.nil.{0} Int))))
                                μ' (Light.sortTime (@List.length.{0} Int L')) fun (x : Int) =>
                                Light.MergeSort.Sorted μ' a' fr L') →
                    Light.Ends lim P d (Light.sortBody pSort pHalf pMerge pCopy)
                      {
                        loc :=
                          Light.frame
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int L))
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr) (@List.nil.{0} Int)))),
                        mem := μ }
                      (Light.sortTime (@List.length.{0} Int L)) fun (σ' : Light.State) =>
                      Light.MergeSort.Sorted μ a fr L σ'.mem := by
  exact @Light.MergeSort.body_ends_sourceProof

#print axioms solution
