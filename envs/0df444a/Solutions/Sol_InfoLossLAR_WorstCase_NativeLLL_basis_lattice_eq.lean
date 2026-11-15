-- Prove2me | solution 1 for InfoLossLAR.WorstCase.NativeLLL.basis_lattice_eq
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T04:41:03.327293+00:00
-- url     : https://prove2.me/submissions/e2315bc7-89f7-4822-a453-2687a1258ceb

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_LARLLL_CurrentData
import Definitions.Def_LARLLL_Foundation01
import Definitions.Def_LARLLL_GramSchmidtRational
import Definitions.Def_LARLLL_KernelTransport
import Definitions.Def_LARLLL_NativeLLLData
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Init
import Init.Data.List.Sort.Basic
import Init.Grind.Ring.Field
import Lean
import Mathlib
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Vector.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.Hom.Set
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic
import Std
import Std.Data.ExtTreeMap.Lemmas

namespace P2MLLL.t0e4be313
end P2MLLL.t0e4be313
section


set_option autoImplicit true



section

/-!
General `List.foldl` algebra shared across the Mathlib-free `hex` libraries.

The computational libraries repeatedly fold an accumulator with a single
operation, `xs.foldl (fun acc x => acc + f x) z` or its multiplicative twin.
Lean core already proves the underlying facts — {name}`List.foldl_assoc`,
{name}`List.sum_eq_foldl`, `List.foldl_map` — but those need `Std.Associative` /
`Std.LawfulIdentity` instances on the carrier, which a bare
`Lean.Grind.Semiring` does not carry. This module supplies those four
instances **file-locally** (just enough to prove the lemmas below) and then
states the fold-algebra the libraries actually use.

The lemmas live in the `List` namespace and follow the standard-library
naming: name the operation, not the use site (`foldl_add_*`, `foldl_mul_*`),
mirror {name}`List.foldl_assoc`/`List.foldl_map`, and keep `foldl_add_eq_add_foldl`
symmetric with `foldl_mul_eq_mul_foldl`. The one exception is
`foldl_const_step`: core/Mathlib already use `List.foldl_const` for the
unrelated iterate lemma, so reusing that name here would collide in the
Theory layers (which import both this module and Mathlib). These are
kept here so the computational libraries can use them without importing
Mathlib.
-/

namespace List

universe u v w

variable {α : Type v} {β : Type w} {R : Type u}

/-!
The `Std.Associative` / `Std.LawfulIdentity` instances that
{name}`List.foldl_assoc` and friends need are kept **file-local**: they are used
only to prove the lemmas below, whose conclusions use `Lean.Grind.Semiring`,
with `Ring` or `CommRing` required only where negation or commutative
multiplication is genuinely involved. Keeping them local avoids adding a
second global `Std.Associative` resolution path for every `Grind.Semiring`
(e.g. `Nat`/`Int` in the theory layers, where Mathlib already supplies
its own). Promote / upstream them separately if a consumer ever needs them.
-/

attribute [local instance] _root_.List.instAssociativeHAdd_solutions








/-! # Congruence -/









/-! # Constant step -/



/-! # Permutation invariance -/





section Semiring

variable [Lean.Grind.Semiring R]

/-! # Accumulator extraction -/

set_option maxRecDepth 8192
/-- Pull the running accumulator out of an additive fold-sum, taking the sum
from a `0` start. The additive twin of {name}`foldl_mul_eq_mul_foldl`. -/
theorem _root_.P2MLLL.t0e4be313.h32 (xs : List α) (f : α → R) (z : R) :
    xs.foldl (fun acc x => acc + f x) z
      = z + xs.foldl (fun acc x => acc + f x) 0 :=
  calc xs.foldl (fun acc x => acc + f x) z
      = (xs.map f).foldl (· + ·) z :=
        (List.foldl_map (l := xs) (f := f) (g := (· + ·)) (init := z)).symm
    _ = (xs.map f).foldl (· + ·) (z + 0) := by rw [Lean.Grind.Semiring.add_zero]
    _ = z + (xs.map f).foldl (· + ·) 0 := List.foldl_assoc
    _ = z + xs.foldl (fun acc x => acc + f x) 0 := by
        rw [List.foldl_map (l := xs) (f := f) (g := (· + ·)) (init := 0)]
open _root_.P2MLLL.t0e4be313 renaming h32 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t0e4be313 renaming h32 → _p2mH32


/-! # All-zero collapse -/



set_option maxRecDepth 8192
/-- An additive fold-sum whose body adds a literal `0` returns the initial
accumulator. -/
theorem _root_.P2MLLL.t0e4be313.h34 (xs : List α) (z : R) :
    xs.foldl (fun acc _ => acc + 0) z = z :=
  foldl_add_eq_self xs (fun _ => 0) z fun _ _ => rfl
open _root_.P2MLLL.t0e4be313 renaming h34 → List.foldl_add_zero
open _root_.P2MLLL.t0e4be313 renaming h34 → _p2mH34


/-! # Scalar factoring -/





set_option maxRecDepth 8192
/-- Factor a right scalar out of an additive fold-sum (right distributivity,
no commutativity needed). -/
theorem _root_.P2MLLL.t0e4be313.h33 (xs : List α) (f : α → R) (c z : R) :
    xs.foldl (fun acc x => acc + f x) z * c =
      xs.foldl (fun acc x => acc + f x * c) (z * c) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (z := z + f x), show (z + f x) * c = z * c + f x * c by grind]
open _root_.P2MLLL.t0e4be313 renaming h33 → List.foldl_add_mul_right
open _root_.P2MLLL.t0e4be313 renaming h33 → _p2mH33


end Semiring
open _root_.P2MLLL.t0e4be313 renaming h32 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t0e4be313 renaming h32 → _p2mH32
open _root_.P2MLLL.t0e4be313 renaming h33 → List.foldl_add_mul_right
open _root_.P2MLLL.t0e4be313 renaming h33 → _p2mH33
open _root_.P2MLLL.t0e4be313 renaming h34 → List.foldl_add_zero
open _root_.P2MLLL.t0e4be313 renaming h34 → _p2mH34


section Ring

variable [Lean.Grind.Ring R]

/-! # Negation -/



end Ring

section Semiring

variable [Lean.Grind.Semiring R]

/-! # Additivity -/



set_option maxRecDepth 8192
/-- An additive fold-sum of a pointwise sum splits into two folds, given a
splitting of the starting accumulator. -/
theorem _root_.P2MLLL.t0e4be313.h30 (xs : List α) (f g : α → R) (acc accF accG : R)
    (h : acc = accF + accG) :
    xs.foldl (fun acc x => acc + (f x + g x)) acc =
      xs.foldl (fun acc x => acc + f x) accF + xs.foldl (fun acc x => acc + g x) accG := by
  subst h
  exact foldl_add_add_start xs f g accF accG
open _root_.P2MLLL.t0e4be313 renaming h30 → List.foldl_add_add_of_acc
open _root_.P2MLLL.t0e4be313 renaming h30 → _p2mH30




end Semiring
open _root_.P2MLLL.t0e4be313 renaming h30 → List.foldl_add_add_of_acc
open _root_.P2MLLL.t0e4be313 renaming h30 → _p2mH30


section Ring

variable [Lean.Grind.Ring R]

/-! # Subtraction -/





end Ring

section Semiring

variable [Lean.Grind.Semiring R]

/-! # Fubini -/

set_option maxRecDepth 8192
/-- Sum-swap (Fubini) for nested additive fold-sums. -/
theorem _root_.P2MLLL.t0e4be313.h31 {γ : Type w} (xs : List α) (ys : List γ) (f : α → γ → R) :
    xs.foldl (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 =
      ys.foldl (fun acc y => acc + xs.foldl (fun acc' x => acc' + f x y) 0) 0 := by
  induction xs with
  | nil =>
    simp only [List.foldl_nil]
    exact (_root_.P2MLLL.t0e4be313.h34 ys 0).symm
  | cons x xs ih =>
    have hLHS :
        (x :: xs).foldl
            (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 =
          ys.foldl (fun acc' y => acc' + f x y) 0 +
            xs.foldl
              (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 := by
      simp only [List.foldl_cons]
      rw [_root_.P2MLLL.t0e4be313.h32 xs
            (fun x' => ys.foldl (fun acc' y => acc' + f x' y) 0)
            (0 + ys.foldl (fun acc' y => acc' + f x y) 0)]
      grind
    have hRHS :
        ys.foldl
            (fun acc y => acc + (x :: xs).foldl
              (fun acc' x' => acc' + f x' y) 0) 0 =
          ys.foldl (fun acc' y => acc' + f x y) 0 +
            ys.foldl
              (fun acc y => acc + xs.foldl
                (fun acc' x' => acc' + f x' y) 0) 0 := by
      have hfun :
          (fun (acc : R) y =>
              acc + (x :: xs).foldl (fun acc' x' => acc' + f x' y) 0) =
            (fun (acc : R) y =>
              acc + (f x y + xs.foldl (fun acc' x' => acc' + f x' y) 0)) := by
        funext acc y
        congr 1
        simp only [List.foldl_cons]
        rw [_root_.P2MLLL.t0e4be313.h32 xs (fun x' => f x' y) (0 + f x y)]
        grind
      rw [hfun]
      exact foldl_add_add ys (fun y => f x y)
        (fun y => xs.foldl (fun acc' x' => acc' + f x' y) 0)
    rw [hLHS, hRHS, ih]
open _root_.P2MLLL.t0e4be313 renaming h31 → List.foldl_add_comm
open _root_.P2MLLL.t0e4be313 renaming h31 → _p2mH31


end Semiring
open _root_.P2MLLL.t0e4be313 renaming h31 → List.foldl_add_comm
open _root_.P2MLLL.t0e4be313 renaming h31 → _p2mH31


section Semiring

variable [Lean.Grind.Semiring R]



end Semiring

/-! # flatMap -/



/-! # Indicator pickout -/



/-! # Monotone bounds (`Nat`) -/









/-! # Multiplicative twins -/



section CommSemiring

variable [Lean.Grind.CommSemiring R]







end CommSemiring

end List
open _root_.P2MLLL.t0e4be313 renaming h30 → List.foldl_add_add_of_acc
open _root_.P2MLLL.t0e4be313 renaming h30 → _p2mH30
open _root_.P2MLLL.t0e4be313 renaming h31 → List.foldl_add_comm
open _root_.P2MLLL.t0e4be313 renaming h31 → _p2mH31
open _root_.P2MLLL.t0e4be313 renaming h32 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t0e4be313 renaming h32 → _p2mH32
open _root_.P2MLLL.t0e4be313 renaming h33 → List.foldl_add_mul_right
open _root_.P2MLLL.t0e4be313 renaming h33 → _p2mH33
open _root_.P2MLLL.t0e4be313 renaming h34 → List.foldl_add_zero
open _root_.P2MLLL.t0e4be313 renaming h34 → _p2mH34


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t0e4be313 renaming h30 → List.foldl_add_add_of_acc
open _root_.P2MLLL.t0e4be313 renaming h30 → _p2mH30
open _root_.P2MLLL.t0e4be313 renaming h31 → List.foldl_add_comm
open _root_.P2MLLL.t0e4be313 renaming h31 → _p2mH31
open _root_.P2MLLL.t0e4be313 renaming h32 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t0e4be313 renaming h32 → _p2mH32
open _root_.P2MLLL.t0e4be313 renaming h33 → List.foldl_add_mul_right
open _root_.P2MLLL.t0e4be313 renaming h33 → _p2mH33
open _root_.P2MLLL.t0e4be313 renaming h34 → List.foldl_add_zero
open _root_.P2MLLL.t0e4be313 renaming h34 → _p2mH34

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section


set_option autoImplicit true



section

/-!
Core dense matrix definitions for `hex-matrix`.

This module models matrices with a **flat row-major** backing `Vector R (n * m)`
and provides the basic executable operations needed by later linear-algebra
algorithms: row/column accessors, zero and identity matrices, dot products,
matrix-vector multiplication, matrix-matrix multiplication, and norm-squared
helpers.

The backing is a single contiguous buffer holding the `n * m` entries in
row-major order: entry `(i, j)` lives at flat index `i * m + j`. The structure
stays an opaque one-field record so this representation is invisible to
consumers, who go through `ofFn`/`ofRows`/`getRow`/`rows` and the entry accessor
`M[(i, j)]`.
-/
namespace Hex

universe u v







end Hex

namespace Vector













end Vector

namespace Hex

namespace Matrix

variable {R : Type u} {n m k : Nat}

/-! # Flat-index arithmetic

Row-major flattening sends entry `(i, j)` to flat index `i * m + j`. These
helpers give the in-range bound and recover `i`, `j` from the flat index. -/











/-! # Entry and row access

Both entry accessors and `getRow` read the flat buffer directly at `i * m + j`,
so a single-entry read is `O(1)` and never materializes a row. -/



















/-! # Core reduction lemmas -/











































/-! # In-place row mutation

The elementary operations update the single backing buffer in place when the
matrix is uniquely referenced. `writeRow` overwrites the `m` entries of one row;
`swapRows` exchanges two rows; both mutate the buffer through `Vector.set` /
`Vector.swap`, which reuse the store rather than copying it when the buffer is
owned. -/

















/-! # Scatter characterizations of the in-place row loops

`writeRow` and the `swap` loop are `Fin.foldl`s of per-column single-index
updates into the flat buffer. Distinct fold steps touch distinct flat indices
(`i * m + t` determines `(i, t)` by `flatIdx_div` / `flatIdx_mod`), so each loop
is characterized by an entrywise read lemma, proved by the same
list-induction-over-`finRange` scheme as `Vector.getElem_finFoldl_modify`. -/





































































set_option maxRecDepth 8192
/-- The `i`-th column of `transpose M` is the `i`-th row of `M`. -/
@[simp, grind =] theorem _root_.P2MLLL.t0e4be313.h8 (M : Matrix R n m) (i : Fin n) :
    col (transpose M) i = row M i := by
  ext k hk
  show (col (transpose M) i)[(⟨k, hk⟩ : Fin m)] = (row M i)[(⟨k, hk⟩ : Fin m)]
  rw [getElem_col, getElem_transpose, getElem_row]
open _root_.P2MLLL.t0e4be313 renaming h8 → Hex.Matrix.col_transpose
open _root_.P2MLLL.t0e4be313 renaming h8 → _p2mH8






















set_option maxRecDepth 8192
/-- Entry characterization for matrix multiplication. -/
@[grind =] theorem _root_.P2MLLL.t0e4be313.h10 [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (N : Matrix R m k) (i : Fin n) (j : Fin k) :
    (M * N)[i][j] = (row M i).dotProduct (col N j) := by
  show (mul M N)[i][j] = (row M i).dotProduct (col N j)
  rw [mul, getElem_ofFn]
open _root_.P2MLLL.t0e4be313 renaming h10 → Hex.Matrix.getElem_mul
open _root_.P2MLLL.t0e4be313 renaming h10 → _p2mH10






set_option maxRecDepth 8192
/-- The identity matrix entry function: `(identity n)[i][j] = 1` if `i = j`, else `0`. -/
@[grind =] theorem _root_.P2MLLL.t0e4be313.h9 [OfNat R 0] [OfNat R 1] {n : Nat} (i j : Fin n) :
    (Matrix.identity (R := R) n)[i][j] = if i = j then (1 : R) else 0 := by
  show (ofFn (fun i j => if i = j then (1 : R) else 0))[i][j] = if i = j then (1 : R) else 0
  rw [getElem_ofFn]
open _root_.P2MLLL.t0e4be313 renaming h9 → Hex.Matrix.getElem_identity
open _root_.P2MLLL.t0e4be313 renaming h9 → _p2mH9














set_option maxRecDepth 8192
/-- A left fold of per-index `swap`s leaves untouched every position not among
the swapped index pairs. -/
 theorem _root_.P2MLLL.t0e4be313.h38 {N : Nat} (idxA idxB : Fin m → Nat)
    (bdA : ∀ t, idxA t < N) (bdB : ∀ t, idxB t < N) {p : Nat} (hp : p < N) :
    ∀ (xs : List (Fin m)) (d0 : Vector R N), (∀ t ∈ xs, idxA t ≠ p ∧ idxB t ≠ p) →
      (xs.foldl (fun d t => d.swap (idxA t) (idxB t) (bdA t) (bdB t)) d0)[p]'hp
        = d0[p]'hp := by
  intro xs
  induction xs with
  | nil => intro d0 _; rfl
  | cons x xs ih =>
    intro d0 hne
    rw [List.foldl_cons, ih _ (fun t ht => hne t (List.mem_cons_of_mem _ ht)),
      Vector.getElem_swap, if_neg (fun heq => (hne x List.mem_cons_self).1 heq.symm),
      if_neg (fun heq => (hne x List.mem_cons_self).2 heq.symm)]
open _root_.P2MLLL.t0e4be313 renaming h38 → Hex.Matrix.foldl_swap_ne
open _root_.P2MLLL.t0e4be313 renaming h38 → _p2mH38


set_option maxRecDepth 8192
/-- A left fold of per-index `swap`s at pairwise-disjoint index pairs over a
`Nodup` list exchanges the pair values at every member index. -/
 theorem _root_.P2MLLL.t0e4be313.h37 {N : Nat} (idxA idxB : Fin m → Nat)
    (bdA : ∀ t, idxA t < N) (bdB : ∀ t, idxB t < N)
    (hdisj : ∀ a b : Fin m, a ≠ b →
      idxA a ≠ idxA b ∧ idxA a ≠ idxB b ∧ idxB a ≠ idxA b ∧ idxB a ≠ idxB b) :
    ∀ (xs : List (Fin m)), xs.Nodup → ∀ (d0 : Vector R N) (r : Fin m), r ∈ xs →
      (xs.foldl (fun d t => d.swap (idxA t) (idxB t) (bdA t) (bdB t)) d0)[idxA r]'(bdA r)
          = d0[idxB r]'(bdB r) ∧
      (xs.foldl (fun d t => d.swap (idxA t) (idxB t) (bdA t) (bdB t)) d0)[idxB r]'(bdB r)
          = d0[idxA r]'(bdA r) := by
  intro xs
  induction xs with
  | nil => intro _ d0 r hr; simp at hr
  | cons x xs ih =>
    intro hnd d0 r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · have hnotail : ∀ t ∈ xs, t ≠ r := fun t ht heq =>
        (List.nodup_cons.mp hnd).1 (heq ▸ ht)
      constructor
      · rw [_root_.P2MLLL.t0e4be313.h38 idxA idxB bdA bdB (bdA r) xs _ (fun t ht =>
          ⟨(hdisj t r (hnotail t ht)).1, (hdisj t r (hnotail t ht)).2.2.1⟩),
          Vector.getElem_swap, if_pos rfl]
      · rw [_root_.P2MLLL.t0e4be313.h38 idxA idxB bdA bdB (bdB r) xs _ (fun t ht =>
          ⟨(hdisj t r (hnotail t ht)).2.1, (hdisj t r (hnotail t ht)).2.2.2⟩),
          Vector.getElem_swap]
        by_cases hab : idxB r = idxA r
        · rw [if_pos hab]
          simp only [hab]
        · rw [if_neg hab, if_pos rfl]
    · have hxr : x ≠ r := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hr')
      have hd := hdisj x r hxr
      obtain ⟨h1, h2⟩ := ih (List.nodup_cons.mp hnd).2
        (d0.swap (idxA x) (idxB x) (bdA x) (bdB x)) r hr'
      constructor
      · rw [h1, Vector.getElem_swap, if_neg (fun heq => hd.2.1 heq.symm),
          if_neg (fun heq => hd.2.2.2 heq.symm)]
      · rw [h2, Vector.getElem_swap, if_neg (fun heq => hd.1 heq.symm),
          if_neg (fun heq => hd.2.2.1 heq.symm)]
open _root_.P2MLLL.t0e4be313 renaming h37 → Hex.Matrix.foldl_swap_mem
open _root_.P2MLLL.t0e4be313 renaming h37 → _p2mH37


set_option maxRecDepth 8192
/-- Flat index pairs of two distinct rows are pairwise disjoint across distinct
columns (and within a column, across the two rows). -/
 theorem _root_.P2MLLL.t0e4be313.h36 {i j : Nat} (hij : i ≠ j) :
    ∀ a b : Fin m, a ≠ b →
      i * m + a.val ≠ i * m + b.val ∧ i * m + a.val ≠ j * m + b.val ∧
      j * m + a.val ≠ i * m + b.val ∧ j * m + a.val ≠ j * m + b.val := by
  intro a b hab
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  refine ⟨fun h => hv (by omega), fun h => ?_, fun h => ?_, fun h => hv (by omega)⟩
  · have h1 : (i * m + a.val) / m = i := flatIdx_div a.isLt
    have h2 : (j * m + b.val) / m = j := flatIdx_div b.isLt
    rw [h, h2] at h1
    exact hij h1.symm
  · have h1 : (j * m + a.val) / m = j := flatIdx_div a.isLt
    have h2 : (i * m + b.val) / m = i := flatIdx_div b.isLt
    rw [h, h2] at h1
    exact hij h1
open _root_.P2MLLL.t0e4be313 renaming h36 → Hex.Matrix.flatIdx_swap_disj
open _root_.P2MLLL.t0e4be313 renaming h36 → _p2mH36


set_option maxRecDepth 8192
@[simp, grind =] theorem _root_.P2MLLL.t0e4be313.h21 (M : Matrix R n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    (M.swap i j hi hj).rows = M.rows.swap i j hi hj := by
  obtain ⟨d⟩ := M
  by_cases hij : i = j
  · subst hij
    apply Vector.ext
    intro r hr
    rw [getElem_rows, Vector.getElem_swap]
    have hswap : ∀ t : Fin m, ∀ (dd : Vector R (n * m)),
        dd.swap (i * m + t.val) (i * m + t.val) (flatIdx_lt hi t.isLt) (flatIdx_lt hi t.isLt)
          = dd := by
      intro t dd
      apply Vector.ext
      intro p hp
      rw [Vector.getElem_swap]
      by_cases hpt : p = i * m + t.val
      · subst hpt
        rw [if_pos rfl]
      · rw [if_neg hpt, if_neg hpt]
    have hid : (swap (⟨d⟩ : Matrix R n m) i i hi hi).data = d := by
      simp only [swap]
      rw [Fin.foldl_eq_finRange_foldl]
      generalize List.finRange m = xs
      induction xs with
      | nil => rfl
      | cons x xs ihx => rw [List.foldl_cons, hswap x d]; exact ihx
    apply Vector.ext
    intro t ht
    rw [getElem_getRow_nat]
    show (swap (⟨d⟩ : Matrix R n m) i i hi hi).data[r * m + t]'(flatIdx_lt hr ht) = _
    rw [hid]
    by_cases hri : r = i
    · rw [if_pos hri, getElem_rows, getElem_getRow_nat]
      simp only [hri]
    · rw [if_neg hri, if_neg hri, getElem_rows, getElem_getRow_nat]
  · apply Vector.ext
    intro r hr
    rw [getElem_rows, Vector.getElem_swap]
    have hfold : (swap (⟨d⟩ : Matrix R n m) i j hi hj).data =
        (List.finRange m).foldl
          (fun dd (t : Fin m) => dd.swap (i * m + t.val) (j * m + t.val)
            (flatIdx_lt hi t.isLt) (flatIdx_lt hj t.isLt)) d := by
      simp only [swap]
      rw [Fin.foldl_eq_finRange_foldl]
    by_cases hri : r = i
    · subst hri
      rw [if_pos rfl]
      apply Vector.ext
      intro t ht
      rw [getElem_getRow_nat, getElem_rows, getElem_getRow_nat]
      show (swap (⟨d⟩ : Matrix R n m) r j hr hj).data[r * m + t]'(flatIdx_lt hr ht) = _
      rw [hfold]
      exact (_root_.P2MLLL.t0e4be313.h37 _ _ (fun s => flatIdx_lt hr s.isLt) (fun s => flatIdx_lt hj s.isLt)
        (_root_.P2MLLL.t0e4be313.h36 hij) (List.finRange m) (nodup_finRange m) d ⟨t, ht⟩
        (List.mem_finRange _)).1
    · by_cases hrj : r = j
      · subst hrj
        rw [if_neg hri, if_pos rfl]
        apply Vector.ext
        intro t ht
        rw [getElem_getRow_nat, getElem_rows, getElem_getRow_nat]
        show (swap (⟨d⟩ : Matrix R n m) i r hi hr).data[r * m + t]'(flatIdx_lt hr ht) = _
        rw [hfold]
        exact (_root_.P2MLLL.t0e4be313.h37 _ _ (fun s => flatIdx_lt hi s.isLt) (fun s => flatIdx_lt hr s.isLt)
          (_root_.P2MLLL.t0e4be313.h36 hij) (List.finRange m) (nodup_finRange m) d ⟨t, ht⟩
          (List.mem_finRange _)).2
      · rw [if_neg hri, if_neg hrj, getElem_rows]
        apply Vector.ext
        intro t ht
        rw [getElem_getRow_nat, getElem_getRow_nat]
        show (swap (⟨d⟩ : Matrix R n m) i j hi hj).data[r * m + t]'(flatIdx_lt hr ht) = _
        rw [hfold]
        exact _root_.P2MLLL.t0e4be313.h38 _ _ (fun s => flatIdx_lt hi s.isLt) (fun s => flatIdx_lt hj s.isLt)
          (flatIdx_lt hr ht) (List.finRange m) d (fun s _ => by
            constructor
            · intro heq
              have h1 : (i * m + s.val) / m = i := flatIdx_div s.isLt
              have h2 : (r * m + t) / m = r := flatIdx_div ht
              rw [heq, h2] at h1
              exact hri h1
            · intro heq
              have h1 : (j * m + s.val) / m = j := flatIdx_div s.isLt
              have h2 : (r * m + t) / m = r := flatIdx_div ht
              rw [heq, h2] at h1
              exact hrj h1)
open _root_.P2MLLL.t0e4be313 renaming h21 → Hex.Matrix.rows_swap
open _root_.P2MLLL.t0e4be313 renaming h21 → _p2mH21




































end Matrix
open _root_.P2MLLL.t0e4be313 renaming h8 → Hex.Matrix.col_transpose
open _root_.P2MLLL.t0e4be313 renaming h8 → _p2mH8
open _root_.P2MLLL.t0e4be313 renaming h9 → Hex.Matrix.getElem_identity
open _root_.P2MLLL.t0e4be313 renaming h9 → _p2mH9
open _root_.P2MLLL.t0e4be313 renaming h10 → Hex.Matrix.getElem_mul
open _root_.P2MLLL.t0e4be313 renaming h10 → _p2mH10
open _root_.P2MLLL.t0e4be313 renaming h21 → Hex.Matrix.rows_swap
open _root_.P2MLLL.t0e4be313 renaming h21 → _p2mH21
open _root_.P2MLLL.t0e4be313 renaming h36 → Hex.Matrix.flatIdx_swap_disj
open _root_.P2MLLL.t0e4be313 renaming h36 → _p2mH36
open _root_.P2MLLL.t0e4be313 renaming h37 → Hex.Matrix.foldl_swap_mem
open _root_.P2MLLL.t0e4be313 renaming h37 → _p2mH37
open _root_.P2MLLL.t0e4be313 renaming h38 → Hex.Matrix.foldl_swap_ne
open _root_.P2MLLL.t0e4be313 renaming h38 → _p2mH38

end Hex
open _root_.P2MLLL.t0e4be313 renaming h8 → Hex.Matrix.col_transpose
open _root_.P2MLLL.t0e4be313 renaming h8 → _p2mH8
open _root_.P2MLLL.t0e4be313 renaming h9 → Hex.Matrix.getElem_identity
open _root_.P2MLLL.t0e4be313 renaming h9 → _p2mH9
open _root_.P2MLLL.t0e4be313 renaming h10 → Hex.Matrix.getElem_mul
open _root_.P2MLLL.t0e4be313 renaming h10 → _p2mH10
open _root_.P2MLLL.t0e4be313 renaming h21 → Hex.Matrix.rows_swap
open _root_.P2MLLL.t0e4be313 renaming h21 → _p2mH21
open _root_.P2MLLL.t0e4be313 renaming h36 → Hex.Matrix.flatIdx_swap_disj
open _root_.P2MLLL.t0e4be313 renaming h36 → _p2mH36
open _root_.P2MLLL.t0e4be313 renaming h37 → Hex.Matrix.foldl_swap_mem
open _root_.P2MLLL.t0e4be313 renaming h37 → _p2mH37
open _root_.P2MLLL.t0e4be313 renaming h38 → Hex.Matrix.foldl_swap_ne
open _root_.P2MLLL.t0e4be313 renaming h38 → _p2mH38


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t0e4be313 renaming h8 → Hex.Matrix.col_transpose
open _root_.P2MLLL.t0e4be313 renaming h8 → _p2mH8
open _root_.P2MLLL.t0e4be313 renaming h9 → Hex.Matrix.getElem_identity
open _root_.P2MLLL.t0e4be313 renaming h9 → _p2mH9
open _root_.P2MLLL.t0e4be313 renaming h10 → Hex.Matrix.getElem_mul
open _root_.P2MLLL.t0e4be313 renaming h10 → _p2mH10
open _root_.P2MLLL.t0e4be313 renaming h21 → Hex.Matrix.rows_swap
open _root_.P2MLLL.t0e4be313 renaming h21 → _p2mH21

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section



set_option autoImplicit true



section

/-!
Elementary row and column operations.

This module contains the primitive executable row/column operations and their
entrywise access lemmas. Algebraic preservation theorems for multiplication and
inverse tracking live downstream in `HexRowReduce.RowEchelon`.
-/

namespace Hex

universe u

namespace Matrix

set_option maxRecDepth 8192
/-- Reading the `i`-th materialized row of `M.rows` is `getRow M i`. A stable
bridge (independent of the backing representation) used to route the entrywise
elementary-op proofs through the `.rows` characterization lemmas. -/
 theorem _root_.P2MLLL.t0e4be313.h39 (M : Matrix R n m) (i : Fin n) : M.rows[i] = getRow M i := by
  simp [rows]
open _root_.P2MLLL.t0e4be313 renaming h39 → Hex.Matrix.getRow_rows
open _root_.P2MLLL.t0e4be313 renaming h39 → _p2mH39






set_option maxRecDepth 8192
/-- Read an entry of `rowSwap M i j` by cases on the row index: row `j`
returns the original row `i`, row `i` returns the original row `j`, and any
other row is unchanged. -/
theorem _root_.P2MLLL.t0e4be313.h12 (M : Matrix R n m) (i j r : Fin n) (k : Fin m) :
    (rowSwap M i j)[r][k] =
      if r = j then M[i][k] else if r = i then M[j][k] else M[r][k] := by
  rw [rowSwap, getElem_eq_getRow, ← _root_.P2MLLL.t0e4be313.h39, _root_.P2MLLL.t0e4be313.h21]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    simp_all [getElem_eq_getRow, Fin.ext_iff]
open _root_.P2MLLL.t0e4be313 renaming h12 → Hex.Matrix.getElem_rowSwap
open _root_.P2MLLL.t0e4be313 renaming h12 → _p2mH12




















set_option maxRecDepth 8192
/-- Read an entry of `rowAdd M src dst c` by cases on the row index: row `dst`
returns `M[dst][k] + c * M[src][k]`, any other row is unchanged. -/
theorem _root_.P2MLLL.t0e4be313.h11 [Mul R] [Add R]
    (M : Matrix R n m) (src dst r : Fin n) (c : R) (k : Fin m) :
    (rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  rw [rowAdd, getElem_modifyEntries]
  by_cases h : r = dst
  · rw [if_pos (congrArg Fin.val h), if_pos h, h]
    rw [show (getRow M src)[k] = M[src][k] from rfl]
  · rw [if_neg (fun hv => h (Fin.ext hv)), if_neg h]
open _root_.P2MLLL.t0e4be313 renaming h11 → Hex.Matrix.getElem_rowAdd
open _root_.P2MLLL.t0e4be313 renaming h11 → _p2mH11




set_option maxRecDepth 8192
/-- Row `dst` of `rowAdd M src dst c` is the pointwise row combination. -/
@[simp, grind =] theorem _root_.P2MLLL.t0e4be313.h19 [Mul R] [Add R]
    (M : Matrix R n m) (src dst : Fin n) (c : R) :
    row (rowAdd M src dst c) dst =
      Vector.ofFn (fun k => M[dst][k] + c * M[src][k]) := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowAdd M src dst c) dst)[kk] =
    (Vector.ofFn (fun k => M[dst][k] + c * M[src][k]))[kk]
  rw [getElem_row, _root_.P2MLLL.t0e4be313.h11]
  simp
open _root_.P2MLLL.t0e4be313 renaming h19 → Hex.Matrix.row_rowAdd_dst
open _root_.P2MLLL.t0e4be313 renaming h19 → _p2mH19


set_option maxRecDepth 8192
/-- Any row other than `dst` is unchanged by `rowAdd M src dst c`. -/
theorem _root_.P2MLLL.t0e4be313.h20 [Mul R] [Add R]
    (M : Matrix R n m) (src : Fin n) {dst r : Fin n} (c : R)
    (hrdst : r ≠ dst) :
    row (rowAdd M src dst c) r = row M r := by
  ext k hk
  let kk : Fin m := ⟨k, hk⟩
  show (row (rowAdd M src dst c) r)[kk] = (row M r)[kk]
  rw [getElem_row, getElem_row, _root_.P2MLLL.t0e4be313.h11]
  simp [hrdst]
open _root_.P2MLLL.t0e4be313 renaming h20 → Hex.Matrix.row_rowAdd_of_ne
open _root_.P2MLLL.t0e4be313 renaming h20 → _p2mH20






































































end Matrix
open _root_.P2MLLL.t0e4be313 renaming h11 → Hex.Matrix.getElem_rowAdd
open _root_.P2MLLL.t0e4be313 renaming h11 → _p2mH11
open _root_.P2MLLL.t0e4be313 renaming h12 → Hex.Matrix.getElem_rowSwap
open _root_.P2MLLL.t0e4be313 renaming h12 → _p2mH12
open _root_.P2MLLL.t0e4be313 renaming h19 → Hex.Matrix.row_rowAdd_dst
open _root_.P2MLLL.t0e4be313 renaming h19 → _p2mH19
open _root_.P2MLLL.t0e4be313 renaming h20 → Hex.Matrix.row_rowAdd_of_ne
open _root_.P2MLLL.t0e4be313 renaming h20 → _p2mH20
open _root_.P2MLLL.t0e4be313 renaming h39 → Hex.Matrix.getRow_rows
open _root_.P2MLLL.t0e4be313 renaming h39 → _p2mH39


end Hex
open _root_.P2MLLL.t0e4be313 renaming h11 → Hex.Matrix.getElem_rowAdd
open _root_.P2MLLL.t0e4be313 renaming h11 → _p2mH11
open _root_.P2MLLL.t0e4be313 renaming h12 → Hex.Matrix.getElem_rowSwap
open _root_.P2MLLL.t0e4be313 renaming h12 → _p2mH12
open _root_.P2MLLL.t0e4be313 renaming h19 → Hex.Matrix.row_rowAdd_dst
open _root_.P2MLLL.t0e4be313 renaming h19 → _p2mH19
open _root_.P2MLLL.t0e4be313 renaming h20 → Hex.Matrix.row_rowAdd_of_ne
open _root_.P2MLLL.t0e4be313 renaming h20 → _p2mH20
open _root_.P2MLLL.t0e4be313 renaming h39 → Hex.Matrix.getRow_rows
open _root_.P2MLLL.t0e4be313 renaming h39 → _p2mH39


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t0e4be313 renaming h11 → Hex.Matrix.getElem_rowAdd
open _root_.P2MLLL.t0e4be313 renaming h11 → _p2mH11
open _root_.P2MLLL.t0e4be313 renaming h12 → Hex.Matrix.getElem_rowSwap
open _root_.P2MLLL.t0e4be313 renaming h12 → _p2mH12
open _root_.P2MLLL.t0e4be313 renaming h19 → Hex.Matrix.row_rowAdd_dst
open _root_.P2MLLL.t0e4be313 renaming h19 → _p2mH19
open _root_.P2MLLL.t0e4be313 renaming h20 → Hex.Matrix.row_rowAdd_of_ne
open _root_.P2MLLL.t0e4be313 renaming h20 → _p2mH20

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section




set_option autoImplicit true



section

/-!
Algebraic laws for dense matrix multiplication.
-/

namespace Hex

universe u v w

namespace Matrix

set_option maxRecDepth 8192
/-- Folding the indicator-weighted terms `(if i = l then 1 else 0) * f l` over a
duplicate-free list containing `i` picks out exactly `f i`, adding it to the accumulator;
the selection step behind reading a single matrix entry out of a sum. -/
private theorem _root_.P2MLLL.t0e4be313.h41 {R : Type u} [Lean.Grind.Ring R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n) (f : Fin n → R)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : R) :
    xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0) * f l) acc =
      acc + f i := by
  induction xs generalizing acc with
  | nil =>
      exact absurd hi List.not_mem_nil
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hieq | hitail
      · subst i
        have hxs_zero :
            ∀ y ∈ xs, (if x = y then (1 : R) else 0) * f y = 0 := by
          intro y hy
          have hxy : x ≠ y := fun heq => (List.nodup_cons.mp hnodup).1 (heq ▸ hy)
          rw [if_neg hxy]
          grind
        rw [if_pos rfl, List.foldl_add_eq_self xs _ _ hxs_zero]
        grind
      · have hxi : i ≠ x := by
          intro heq
          rw [← heq] at hnodup
          exact (List.nodup_cons.mp hnodup).1 hitail
        rw [if_neg hxi]
        have hzero : (0 : R) * f x = 0 := by grind
        rw [hzero]
        have hac : acc + (0 : R) = acc := by grind
        rw [hac]
        exact ih hitail (List.nodup_cons.mp hnodup).2 acc
open _root_.P2MLLL.t0e4be313 renaming h41 → Hex.Matrix.foldl_indicator_mul_unique
open _root_.P2MLLL.t0e4be313 renaming h41 → _p2mH41




set_option maxRecDepth 8192
/-- Matrix multiplication associates with matrix-vector multiplication. -/
theorem _root_.P2MLLL.t0e4be313.h14 [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (v : Vector R k) :
    (A * B) * v = A * (B * v) := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  show ((A * B) * v)[ii] = (A * (B * v))[ii]
  simp only [getElem_mulVec, _root_.P2MLLL.t0e4be313.h10, getElem_row, getElem_col, Vector.dotProduct]
  change
    (List.finRange k).foldl
        (fun acc l =>
          acc + (List.finRange m).foldl (fun acc j => acc + A[ii][j] * B[j][l]) 0 *
            v[l]) 0 =
      (List.finRange m).foldl
        (fun acc j =>
          acc + A[ii][j] *
            (List.finRange k).foldl (fun acc l => acc + B[j][l] * v[l]) 0) 0
  calc
    (List.finRange k).foldl
        (fun acc l =>
          acc + (List.finRange m).foldl (fun acc j => acc + A[ii][j] * B[j][l]) 0 *
            v[l]) 0 =
        (List.finRange k).foldl
          (fun acc l =>
            acc + (List.finRange m).foldl
              (fun acc j => acc + A[ii][j] * B[j][l] * v[l]) 0) 0 := by
          apply List.foldl_add_congr
          intro l _hl
          rw [_root_.P2MLLL.t0e4be313.h33]
          grind
    _ = (List.finRange m).foldl
        (fun acc j =>
          acc + A[ii][j] *
            (List.finRange k).foldl (fun acc l => acc + B[j][l] * v[l]) 0) 0 := by
          rw [_root_.P2MLLL.t0e4be313.h31]
          apply List.foldl_add_congr
          intro j _hj
          rw [← List.foldl_add_mul_left]
          have hzero : A[ii][j] * (0 : R) = 0 := by grind
          rw [hzero]
          apply List.foldl_add_congr
          intro l _hl
          grind
open _root_.P2MLLL.t0e4be313 renaming h14 → Hex.Matrix.mul_assoc_vec
open _root_.P2MLLL.t0e4be313 renaming h14 → _p2mH14


set_option maxRecDepth 8192
/-- Transpose reverses matrix multiplication over a commutative coefficient type. -/
theorem _root_.P2MLLL.t0e4be313.h22 [Lean.Grind.CommRing R]
    (A : Matrix R n m) (B : Matrix R m k) :
    Matrix.transpose (A * B) = Matrix.transpose B * Matrix.transpose A := by
  apply ext_getElem
  intro ii jj
  rw [getElem_transpose, _root_.P2MLLL.t0e4be313.h10, _root_.P2MLLL.t0e4be313.h10, row_transpose, _root_.P2MLLL.t0e4be313.h8,
    Vector.dotProduct, Vector.dotProduct]
  apply List.foldl_add_congr
  intro l _hl
  rw [Lean.Grind.CommSemiring.mul_comm]
open _root_.P2MLLL.t0e4be313 renaming h22 → Hex.Matrix.transpose_mul_of_mul_comm
open _root_.P2MLLL.t0e4be313 renaming h22 → _p2mH22
















set_option maxRecDepth 8192
/-- Left-multiplication by the identity matrix leaves a matrix unchanged. -/
@[simp, grind =] theorem _root_.P2MLLL.t0e4be313.h13 [Lean.Grind.Ring R] (M : Matrix R n m) :
    (Matrix.identity (R := R) n) * M = M := by
  apply ext_getElem
  intro ii jj
  rw [_root_.P2MLLL.t0e4be313.h10, Vector.dotProduct]
  calc
    (List.finRange n).foldl
        (fun acc l => acc + (row (Matrix.identity (R := R) n) ii)[l] * (col M jj)[l]) 0 =
        (List.finRange n).foldl
          (fun acc l => acc + (if ii = l then (1 : R) else 0) * M[l][jj]) 0 := by
          apply List.foldl_add_congr
          intro l _hl
          rw [getElem_row, getElem_col, _root_.P2MLLL.t0e4be313.h9]
    _ = M[ii][jj] := by
          rw [_root_.P2MLLL.t0e4be313.h41 (List.finRange n) ii (fun l => M[l][jj])
            (List.mem_finRange _) (List.nodup_finRange n) 0]
          grind
open _root_.P2MLLL.t0e4be313 renaming h13 → Hex.Matrix.identity_mul
open _root_.P2MLLL.t0e4be313 renaming h13 → _p2mH13














































end Matrix
open _root_.P2MLLL.t0e4be313 renaming h13 → Hex.Matrix.identity_mul
open _root_.P2MLLL.t0e4be313 renaming h13 → _p2mH13
open _root_.P2MLLL.t0e4be313 renaming h14 → Hex.Matrix.mul_assoc_vec
open _root_.P2MLLL.t0e4be313 renaming h14 → _p2mH14
open _root_.P2MLLL.t0e4be313 renaming h22 → Hex.Matrix.transpose_mul_of_mul_comm
open _root_.P2MLLL.t0e4be313 renaming h22 → _p2mH22
open _root_.P2MLLL.t0e4be313 renaming h41 → Hex.Matrix.foldl_indicator_mul_unique
open _root_.P2MLLL.t0e4be313 renaming h41 → _p2mH41


end Hex
open _root_.P2MLLL.t0e4be313 renaming h13 → Hex.Matrix.identity_mul
open _root_.P2MLLL.t0e4be313 renaming h13 → _p2mH13
open _root_.P2MLLL.t0e4be313 renaming h14 → Hex.Matrix.mul_assoc_vec
open _root_.P2MLLL.t0e4be313 renaming h14 → _p2mH14
open _root_.P2MLLL.t0e4be313 renaming h22 → Hex.Matrix.transpose_mul_of_mul_comm
open _root_.P2MLLL.t0e4be313 renaming h22 → _p2mH22
open _root_.P2MLLL.t0e4be313 renaming h41 → Hex.Matrix.foldl_indicator_mul_unique
open _root_.P2MLLL.t0e4be313 renaming h41 → _p2mH41


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t0e4be313 renaming h13 → Hex.Matrix.identity_mul
open _root_.P2MLLL.t0e4be313 renaming h13 → _p2mH13
open _root_.P2MLLL.t0e4be313 renaming h14 → Hex.Matrix.mul_assoc_vec
open _root_.P2MLLL.t0e4be313 renaming h14 → _p2mH14
open _root_.P2MLLL.t0e4be313 renaming h22 → Hex.Matrix.transpose_mul_of_mul_comm
open _root_.P2MLLL.t0e4be313 renaming h22 → _p2mH22

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section




set_option autoImplicit true



section

/-!
Algebraic properties of elementary row/column operations, shared by matrix clients.

The primitive executable operations live in `HexMatrix.Elementary`. This module
adds the multiplication- and inverse-preservation facts (`rowSwap_mul`,
`rowScale_mul`, `rowAdd_mul`, the `*_transform_mul_preserve` and
`*_inverse_preserve` families, and the column-operation analogues) on which the
row-reduction, span/nullspace, and determinant routines rely.
-/

namespace Hex

universe u

namespace Matrix




set_option maxRecDepth 8192
/-- Distribute the left argument of a dot product over a sum of the form
`Vector.ofFn (fun k => v[k] + s * w[k])`. -/
private theorem _root_.P2MLLL.t0e4be313.h40 [Lean.Grind.Ring R]
    (u v w : Vector R m) (s : R) :
    (Vector.ofFn fun k => u[k] + s * v[k]).dotProduct w =
    u.dotProduct w + s * v.dotProduct w := by
  unfold Vector.dotProduct
  -- LHS body: (u[k] + s * v[k]) * w[k] = u[k] * w[k] + s * (v[k] * w[k])
  rw [show (List.finRange m).foldl
        (fun acc i => acc + (Vector.ofFn fun k => u[k] + s * v[k])[i] * w[i]) 0 =
      (List.finRange m).foldl
        (fun acc i => acc + (u[i] * w[i] + s * (v[i] * w[i]))) 0 from ?_]
  · -- Now split the sum
    have hzero : (0 : R) = 0 + s * 0 := by grind
    rw [_root_.P2MLLL.t0e4be313.h30 (xs := List.finRange m)
          (f := fun i => u[i] * w[i])
          (g := fun i => s * (v[i] * w[i]))
          (acc := 0) (accF := 0) (accG := s * 0) (h := by grind)]
    -- Pull s out of the second sum
    rw [List.foldl_add_mul_left (xs := List.finRange m)
          (f := fun i => v[i] * w[i]) (c := s) (z := 0)]
  · apply List.foldl_add_congr
    intro i _
    have hofFn : (Vector.ofFn (fun k : Fin m => u[k] + s * v[k]))[i] =
        u[i] + s * v[i] := by
      simp
    rw [hofFn]
    grind
open _root_.P2MLLL.t0e4be313 renaming h40 → Hex.Matrix.dotProduct_add_smul_ofFn_left
open _root_.P2MLLL.t0e4be313 renaming h40 → _p2mH40






set_option maxRecDepth 8192
/-- Multiplication by `B` commutes with row swap on the left factor. -/
theorem _root_.P2MLLL.t0e4be313.h17 [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (i j : Fin n) :
    rowSwap A i j * B = rowSwap (A * B) i j := by
  apply ext_getElem
  intro rr ll
  rw [_root_.P2MLLL.t0e4be313.h10 (rowSwap A i j) B rr ll, _root_.P2MLLL.t0e4be313.h12 (A * B) i j rr ll]
  by_cases hrj : rr = j
  · rw [if_pos hrj]
    rw [_root_.P2MLLL.t0e4be313.h10 A B i ll]
    have hrow : (rowSwap A i j)[rr] = A[i] := by
      ext k' hk
      let kk : Fin m := ⟨k', hk⟩
      show (rowSwap A i j)[rr][kk] = A[i][kk]
      rw [_root_.P2MLLL.t0e4be313.h12]; rw [if_pos hrj]
    rw [show row (rowSwap A i j) rr = row A i by simpa [row] using hrow]
  · rw [if_neg hrj]
    by_cases hri : rr = i
    · rw [if_pos hri]
      rw [_root_.P2MLLL.t0e4be313.h10 A B j ll]
      have hrow : (rowSwap A i j)[rr] = A[j] := by
        ext k' hk
        let kk : Fin m := ⟨k', hk⟩
        show (rowSwap A i j)[rr][kk] = A[j][kk]
        rw [_root_.P2MLLL.t0e4be313.h12]; rw [if_neg hrj, if_pos hri]
      rw [show row (rowSwap A i j) rr = row A j by simpa [row] using hrow]
    · rw [if_neg hri]
      rw [_root_.P2MLLL.t0e4be313.h10 A B rr ll]
      have hrow : (rowSwap A i j)[rr] = A[rr] := by
        ext k' hk
        let kk : Fin m := ⟨k', hk⟩
        show (rowSwap A i j)[rr][kk] = A[rr][kk]
        rw [_root_.P2MLLL.t0e4be313.h12]; rw [if_neg hrj, if_neg hri]
      rw [show row (rowSwap A i j) rr = row A rr by simpa [row] using hrow]
open _root_.P2MLLL.t0e4be313 renaming h17 → Hex.Matrix.rowSwap_mul
open _root_.P2MLLL.t0e4be313 renaming h17 → _p2mH17




set_option maxRecDepth 8192
/-- Multiplication by `B` commutes with the row-add operation on the left
factor. -/
theorem _root_.P2MLLL.t0e4be313.h15 [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (src dst : Fin n) (s : R) :
    rowAdd A src dst s * B = rowAdd (A * B) src dst s := by
  apply ext_getElem
  intro rr ll
  rw [_root_.P2MLLL.t0e4be313.h10 (rowAdd A src dst s) B rr ll, _root_.P2MLLL.t0e4be313.h11 (A * B) src dst rr s ll]
  by_cases hrd : rr = dst
  · rw [if_pos hrd]
    rw [_root_.P2MLLL.t0e4be313.h10 A B dst ll, _root_.P2MLLL.t0e4be313.h10 A B src ll]
    rw [show row (rowAdd A src dst s) rr =
        Vector.ofFn (fun k' => A[dst][k'] + s * A[src][k']) by
      rw [hrd]
      exact _root_.P2MLLL.t0e4be313.h19 A src dst s]
    exact _root_.P2MLLL.t0e4be313.h40 A[dst] A[src] (col B ll) s
  · rw [if_neg hrd]
    rw [_root_.P2MLLL.t0e4be313.h10 A B rr ll]
    rw [show row (rowAdd A src dst s) rr = row A rr by
      exact _root_.P2MLLL.t0e4be313.h20 A src s hrd]
open _root_.P2MLLL.t0e4be313 renaming h15 → Hex.Matrix.rowAdd_mul
open _root_.P2MLLL.t0e4be313 renaming h15 → _p2mH15














set_option maxRecDepth 8192
/-- Swapping the same two rows twice restores the original matrix. -/
theorem _root_.P2MLLL.t0e4be313.h18 (M : Matrix R n m) (i j : Fin n) :
    rowSwap (rowSwap M i j) i j = M := by
  apply ext_getElem
  intro rr kk
  rw [_root_.P2MLLL.t0e4be313.h12]
  by_cases hrj : rr = j
  · rw [if_pos hrj]
    rw [_root_.P2MLLL.t0e4be313.h12]
    by_cases hji : i = j
    · simp [hrj, hji]
    · simp [hrj, hji]
  · rw [if_neg hrj]
    by_cases hri : rr = i
    · rw [if_pos hri]
      rw [_root_.P2MLLL.t0e4be313.h12]
      simp [hri]
    · rw [if_neg hri]
      rw [_root_.P2MLLL.t0e4be313.h12, if_neg hrj, if_neg hri]
open _root_.P2MLLL.t0e4be313 renaming h18 → Hex.Matrix.rowSwap_rowSwap
open _root_.P2MLLL.t0e4be313 renaming h18 → _p2mH18












set_option maxRecDepth 8192
/-- Adding `s` times a distinct source row to a destination row and then
adding `-s` times that source row restores the original matrix. -/
theorem _root_.P2MLLL.t0e4be313.h16 [Lean.Grind.Ring R]
    (M : Matrix R n m) {src dst : Fin n} (s : R) (hsrcdst : src ≠ dst) :
    rowAdd (rowAdd M src dst s) src dst (-s) = M := by
  apply ext_getElem
  intro rr kk
  rw [_root_.P2MLLL.t0e4be313.h11]
  by_cases hrd : rr = dst
  · rw [if_pos hrd]
    rw [_root_.P2MLLL.t0e4be313.h11, if_pos rfl]
    have hsrc_ne_dst : src ≠ dst := hsrcdst
    rw [_root_.P2MLLL.t0e4be313.h11, if_neg hsrc_ne_dst]
    grind
  · rw [if_neg hrd]
    rw [_root_.P2MLLL.t0e4be313.h11, if_neg hrd]
open _root_.P2MLLL.t0e4be313 renaming h16 → Hex.Matrix.rowAdd_rowAdd_neg
open _root_.P2MLLL.t0e4be313 renaming h16 → _p2mH16




























end Matrix
open _root_.P2MLLL.t0e4be313 renaming h15 → Hex.Matrix.rowAdd_mul
open _root_.P2MLLL.t0e4be313 renaming h15 → _p2mH15
open _root_.P2MLLL.t0e4be313 renaming h16 → Hex.Matrix.rowAdd_rowAdd_neg
open _root_.P2MLLL.t0e4be313 renaming h16 → _p2mH16
open _root_.P2MLLL.t0e4be313 renaming h17 → Hex.Matrix.rowSwap_mul
open _root_.P2MLLL.t0e4be313 renaming h17 → _p2mH17
open _root_.P2MLLL.t0e4be313 renaming h18 → Hex.Matrix.rowSwap_rowSwap
open _root_.P2MLLL.t0e4be313 renaming h18 → _p2mH18
open _root_.P2MLLL.t0e4be313 renaming h40 → Hex.Matrix.dotProduct_add_smul_ofFn_left
open _root_.P2MLLL.t0e4be313 renaming h40 → _p2mH40

end Hex
open _root_.P2MLLL.t0e4be313 renaming h15 → Hex.Matrix.rowAdd_mul
open _root_.P2MLLL.t0e4be313 renaming h15 → _p2mH15
open _root_.P2MLLL.t0e4be313 renaming h16 → Hex.Matrix.rowAdd_rowAdd_neg
open _root_.P2MLLL.t0e4be313 renaming h16 → _p2mH16
open _root_.P2MLLL.t0e4be313 renaming h17 → Hex.Matrix.rowSwap_mul
open _root_.P2MLLL.t0e4be313 renaming h17 → _p2mH17
open _root_.P2MLLL.t0e4be313 renaming h18 → Hex.Matrix.rowSwap_rowSwap
open _root_.P2MLLL.t0e4be313 renaming h18 → _p2mH18
open _root_.P2MLLL.t0e4be313 renaming h40 → Hex.Matrix.dotProduct_add_smul_ofFn_left
open _root_.P2MLLL.t0e4be313 renaming h40 → _p2mH40


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t0e4be313 renaming h15 → Hex.Matrix.rowAdd_mul
open _root_.P2MLLL.t0e4be313 renaming h15 → _p2mH15
open _root_.P2MLLL.t0e4be313 renaming h16 → Hex.Matrix.rowAdd_rowAdd_neg
open _root_.P2MLLL.t0e4be313 renaming h16 → _p2mH16
open _root_.P2MLLL.t0e4be313 renaming h17 → Hex.Matrix.rowSwap_mul
open _root_.P2MLLL.t0e4be313 renaming h17 → _p2mH17
open _root_.P2MLLL.t0e4be313 renaming h18 → Hex.Matrix.rowSwap_rowSwap
open _root_.P2MLLL.t0e4be313 renaming h18 → _p2mH18

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/




namespace Hex.Matrix
end Hex.Matrix
section



set_option autoImplicit true



section

/-!
Integer row-lattice membership and independence for `hex-lll`,
with the row-operation lemmas showing that an adjacent swap or a
size-reduction row combination preserves the generated lattice.
-/

namespace Hex

namespace Matrix





end Matrix

namespace Internal

open Hex.Matrix

set_option maxRecDepth 8192
/-- `memLattice_of_rowSwap_memLattice` states that any vector in the lattice
generated by `rowSwap b i j` also lies in the lattice generated by `b`. -/
theorem _root_.P2MLLL.t0e4be313.h5
    (b : Matrix Int n m) (i j : Fin n) (v : Vector Int m) :
    Matrix.memLattice (Matrix.rowSwap b i j) v → Matrix.memLattice b v := by
  intro hv
  rcases hv with ⟨c, hc⟩
  let S : Matrix Int n n := Matrix.rowSwap (Matrix.identity (R := Int) n) i j
  have hrow : S * b = Matrix.rowSwap b i j := by
    rw [_root_.P2MLLL.t0e4be313.h17, _root_.P2MLLL.t0e4be313.h13]
  refine ⟨Matrix.transpose S * c, ?_⟩
  calc
    Matrix.vecMul (Matrix.transpose S * c) b
        = Matrix.transpose b * (Matrix.transpose S * c) := rfl
    _ = (Matrix.transpose b * Matrix.transpose S) * c := by
      rw [_root_.P2MLLL.t0e4be313.h14]
    _ = Matrix.transpose (S * b) * c := by
      rw [_root_.P2MLLL.t0e4be313.h22]
    _ = Matrix.transpose (Matrix.rowSwap b i j) * c := by
      rw [hrow]
    _ = Matrix.vecMul c (Matrix.rowSwap b i j) := rfl
    _ = v := hc
open _root_.P2MLLL.t0e4be313 renaming h5 → Hex.Internal.memLattice_of_rowSwap_memLattice
open _root_.P2MLLL.t0e4be313 renaming h5 → _p2mH5


set_option maxRecDepth 8192
/-- `rowSwap_memLattice_iff` states that swapping rows `i` and `j` of `b`
preserves lattice membership in both directions. -/
theorem _root_.P2MLLL.t0e4be313.h7
    (b : Matrix Int n m) (i j : Fin n) (v : Vector Int m) :
    Matrix.memLattice (Matrix.rowSwap b i j) v ↔ Matrix.memLattice b v := by
  constructor
  · exact _root_.P2MLLL.t0e4be313.h5 b i j v
  · intro hv
    have hv' : Matrix.memLattice (Matrix.rowSwap (Matrix.rowSwap b i j) i j) v := by
      rwa [_root_.P2MLLL.t0e4be313.h18]
    exact _root_.P2MLLL.t0e4be313.h5 (Matrix.rowSwap b i j) i j v hv'
open _root_.P2MLLL.t0e4be313 renaming h7 → Hex.Internal.rowSwap_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h7 → _p2mH7


set_option maxRecDepth 8192
/-- `memLattice_of_rowAdd_memLattice` states that any vector in the lattice
generated by `rowAdd b src dst c` also lies in the lattice generated by `b`. -/
theorem _root_.P2MLLL.t0e4be313.h4
    (b : Matrix Int n m) (src dst : Fin n) (c : Int) (v : Vector Int m) :
    Matrix.memLattice (Matrix.rowAdd b src dst c) v → Matrix.memLattice b v := by
  intro hv
  rcases hv with ⟨w, hw⟩
  let S : Matrix Int n n := Matrix.rowAdd (Matrix.identity (R := Int) n) src dst c
  have hrow : S * b = Matrix.rowAdd b src dst c := by
    simp [S, _root_.P2MLLL.t0e4be313.h15, _root_.P2MLLL.t0e4be313.h13]
  refine ⟨Matrix.transpose S * w, ?_⟩
  calc
    Matrix.vecMul (Matrix.transpose S * w) b
        = Matrix.transpose b * (Matrix.transpose S * w) := rfl
    _ = (Matrix.transpose b * Matrix.transpose S) * w := by
      rw [_root_.P2MLLL.t0e4be313.h14]
    _ = Matrix.transpose (S * b) * w := by
      rw [_root_.P2MLLL.t0e4be313.h22]
    _ = Matrix.transpose (Matrix.rowAdd b src dst c) * w := by
      rw [hrow]
    _ = Matrix.vecMul w (Matrix.rowAdd b src dst c) := rfl
    _ = v := hw
open _root_.P2MLLL.t0e4be313 renaming h4 → Hex.Internal.memLattice_of_rowAdd_memLattice
open _root_.P2MLLL.t0e4be313 renaming h4 → _p2mH4


set_option maxRecDepth 8192
/-- `rowAdd_memLattice_iff` states that adding `c` times row `src` to a distinct
row `dst` of `b` preserves lattice membership in both directions. -/
theorem _root_.P2MLLL.t0e4be313.h6
    (b : Matrix Int n m) {src dst : Fin n} (hne : src ≠ dst) (c : Int) (v : Vector Int m) :
    Matrix.memLattice (Matrix.rowAdd b src dst c) v ↔ Matrix.memLattice b v := by
  constructor
  · exact _root_.P2MLLL.t0e4be313.h4 b src dst c v
  · intro hv
    have hv' : Matrix.memLattice
        (Matrix.rowAdd (Matrix.rowAdd b src dst c) src dst (-c)) v := by
      rwa [_root_.P2MLLL.t0e4be313.h16 b c hne]
    exact _root_.P2MLLL.t0e4be313.h4 (Matrix.rowAdd b src dst c) src dst (-c) v hv'
open _root_.P2MLLL.t0e4be313 renaming h6 → Hex.Internal.rowAdd_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h6 → _p2mH6


end Internal
open _root_.P2MLLL.t0e4be313 renaming h4 → Hex.Internal.memLattice_of_rowAdd_memLattice
open _root_.P2MLLL.t0e4be313 renaming h4 → _p2mH4
open _root_.P2MLLL.t0e4be313 renaming h5 → Hex.Internal.memLattice_of_rowSwap_memLattice
open _root_.P2MLLL.t0e4be313 renaming h5 → _p2mH5
open _root_.P2MLLL.t0e4be313 renaming h6 → Hex.Internal.rowAdd_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h6 → _p2mH6
open _root_.P2MLLL.t0e4be313 renaming h7 → Hex.Internal.rowSwap_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h7 → _p2mH7


end Hex
open _root_.P2MLLL.t0e4be313 renaming h4 → Hex.Internal.memLattice_of_rowAdd_memLattice
open _root_.P2MLLL.t0e4be313 renaming h4 → _p2mH4
open _root_.P2MLLL.t0e4be313 renaming h5 → Hex.Internal.memLattice_of_rowSwap_memLattice
open _root_.P2MLLL.t0e4be313 renaming h5 → _p2mH5
open _root_.P2MLLL.t0e4be313 renaming h6 → Hex.Internal.rowAdd_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h6 → _p2mH6
open _root_.P2MLLL.t0e4be313 renaming h7 → Hex.Internal.rowSwap_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h7 → _p2mH7


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t0e4be313 renaming h4 → Hex.Internal.memLattice_of_rowAdd_memLattice
open _root_.P2MLLL.t0e4be313 renaming h4 → _p2mH4
open _root_.P2MLLL.t0e4be313 renaming h5 → Hex.Internal.memLattice_of_rowSwap_memLattice
open _root_.P2MLLL.t0e4be313 renaming h5 → _p2mH5
open _root_.P2MLLL.t0e4be313 renaming h6 → Hex.Internal.rowAdd_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h6 → _p2mH6
open _root_.P2MLLL.t0e4be313 renaming h7 → Hex.Internal.rowSwap_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h7 → _p2mH7

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section


set_option autoImplicit true



section

/-!
The pure integer-arithmetic LLL reducer. `LLLState` carries only the
integer basis, scaled Gram-Schmidt coefficients `ν`, and Gram
determinants `d`; `lllNative` runs the fuel-bounded `d`/`ν` loop, the
trusted exact reducer at the classical `η = 1/2`.
-/

namespace Hex

namespace Internal



namespace LLLState





























set_option maxRecDepth 8192
/-- Adjacent swaps preserve the generated lattice. -/
@[grind =] theorem _root_.P2MLLL.t0e4be313.h2 (s : LLLState n m) (k : Nat) (v : Vector Int m) :
    Matrix.memLattice (s.swapStep k).b v ↔ Matrix.memLattice s.b v := by
  unfold swapStep
  by_cases hk : k < n
  · rw [dif_pos hk]
    by_cases hk0 : 0 < k
    · rw [dif_pos hk0]
      simpa [GramSchmidt.Int.adjacentSwap] using
        _root_.P2MLLL.t0e4be313.h7 s.b (GramSchmidt.prevRow ⟨k, hk⟩ hk0) ⟨k, hk⟩ v
    · rw [dif_neg hk0]
  · rw [dif_neg hk]
open _root_.P2MLLL.t0e4be313 renaming h2 → Hex.Internal.LLLState.swapStep_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h2 → _p2mH2


set_option maxRecDepth 8192
/-- A single-column size reduction preserves the generated lattice. -/
@[grind =] theorem _root_.P2MLLL.t0e4be313.h0
    (s : LLLState n m) (j k : Fin n) (hjk : j.val < k.val) (v : Vector Int m) :
    Matrix.memLattice (s.sizeReduceColumn j k hjk).b v ↔ Matrix.memLattice s.b v := by
  unfold sizeReduceColumn
  by_cases hreduce : 2 * Int.natAbs ((s.ν.getRow k).get j) >
      s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  · rw [dif_pos hreduce]
    have hne : j ≠ k := fun h => Nat.lt_irrefl j.val (h ▸ hjk)
    exact _root_.P2MLLL.t0e4be313.h6 s.b hne _ v
  · rw [dif_neg hreduce]
open _root_.P2MLLL.t0e4be313 renaming h0 → Hex.Internal.LLLState.sizeReduceColumn_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h0 → _p2mH0


set_option maxRecDepth 8192
/-- `sizeReduce_foldl_memLattice_iff` states that folding size-reduction column
steps over a list of columns preserves the integer row-lattice membership
predicate in both directions. -/
private theorem _root_.P2MLLL.t0e4be313.h35 (s : LLLState n m) (k : Nat) (hk : k < n)
    (xs : List (Fin k)) (v : Vector Int m) :
    Matrix.memLattice
        (xs.foldl
          (fun state j =>
            let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
            LLLState.sizeReduceColumn state jFin ⟨k, hk⟩ j.isLt)
          s).b v ↔ Matrix.memLattice s.b v := by
  induction xs generalizing s with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact _root_.P2MLLL.t0e4be313.h0 s _ _ j.isLt v
open _root_.P2MLLL.t0e4be313 renaming h35 → Hex.Internal.LLLState.sizeReduce_foldl_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h35 → _p2mH35


set_option maxRecDepth 8192
/-- Size reduction preserves the generated lattice. -/
@[grind =] theorem _root_.P2MLLL.t0e4be313.h1 (s : LLLState n m) (k : Nat) (v : Vector Int m) :
    Matrix.memLattice (s.sizeReduce k).b v ↔ Matrix.memLattice s.b v := by
  unfold sizeReduce
  by_cases hk : k < n
  · rw [dif_pos hk]
    simpa [Fin.foldr_eq_finRange_foldr] using
      _root_.P2MLLL.t0e4be313.h35 s k hk (List.finRange k).reverse v
  · rw [dif_neg hk]
open _root_.P2MLLL.t0e4be313 renaming h1 → Hex.Internal.LLLState.sizeReduce_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h1 → _p2mH1














end LLLState
open _root_.P2MLLL.t0e4be313 renaming h0 → Hex.Internal.LLLState.sizeReduceColumn_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h0 → _p2mH0
open _root_.P2MLLL.t0e4be313 renaming h1 → Hex.Internal.LLLState.sizeReduce_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h1 → _p2mH1
open _root_.P2MLLL.t0e4be313 renaming h2 → Hex.Internal.LLLState.swapStep_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h2 → _p2mH2
open _root_.P2MLLL.t0e4be313 renaming h35 → Hex.Internal.LLLState.sizeReduce_foldl_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h35 → _p2mH35




set_option maxRecDepth 8192
/-- `lllLoop` preserves the generated lattice: every iteration is either a
`sizeReduce` (preserved by `sizeReduce_memLattice_iff`) or an adjacent swap
(preserved by `swapStep_memLattice_iff`). -/
@[grind =] theorem _root_.P2MLLL.t0e4be313.h3 (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hk : 1 ≤ k) (hkn : k ≤ n) (fuel : Nat)
    (v : Vector Int m) :
    Matrix.memLattice (lllLoop s k δ hδ hδ' hk hkn fuel) v ↔
      Matrix.memLattice s.b v := by
  induction fuel generalizing s k hk hkn with
  | zero => rfl
  | succ f ih =>
    show Matrix.memLattice
      (if hdone : k = n then s.b else _) v ↔ _
    by_cases hdone : k = n
    · rw [dif_pos hdone]
    · rw [dif_neg hdone]
      by_cases hcond : Int.ofNat δ.den *
            (Int.ofNat ((s.sizeReduce k).d.get
                ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_le_of_ne hkn hdone)⟩) *
              Int.ofNat ((s.sizeReduce k).d.get
                ⟨k - 1, Nat.lt_trans
                  (Nat.lt_of_le_of_lt (Nat.sub_le k 1)
                    (Nat.lt_of_le_of_ne hkn hdone))
                  (Nat.lt_succ_self n)⟩) +
              ((s.sizeReduce k).ν.getRow ⟨k, Nat.lt_of_le_of_ne hkn hdone⟩).get
                ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1)
                  (Nat.lt_of_le_of_ne hkn hdone)⟩ ^ 2) ≥
          δ.num * (Int.ofNat ((s.sizeReduce k).d.get
            ⟨k, Nat.lt_succ_of_lt (Nat.lt_of_le_of_ne hkn hdone)⟩) ^ 2)
      · rw [if_pos hcond, ih, _root_.P2MLLL.t0e4be313.h1]
      · rw [if_neg hcond, ih, _root_.P2MLLL.t0e4be313.h2,
          _root_.P2MLLL.t0e4be313.h1]
open _root_.P2MLLL.t0e4be313 renaming h3 → Hex.Internal.lllLoop_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h3 → _p2mH3






end Internal
open _root_.P2MLLL.t0e4be313 renaming h0 → Hex.Internal.LLLState.sizeReduceColumn_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h0 → _p2mH0
open _root_.P2MLLL.t0e4be313 renaming h1 → Hex.Internal.LLLState.sizeReduce_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h1 → _p2mH1
open _root_.P2MLLL.t0e4be313 renaming h2 → Hex.Internal.LLLState.swapStep_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h2 → _p2mH2
open _root_.P2MLLL.t0e4be313 renaming h3 → Hex.Internal.lllLoop_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h3 → _p2mH3
open _root_.P2MLLL.t0e4be313 renaming h35 → Hex.Internal.LLLState.sizeReduce_foldl_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h35 → _p2mH35


open Hex.Internal



namespace Internal



end Internal

end Hex
open _root_.P2MLLL.t0e4be313 renaming h0 → Hex.Internal.LLLState.sizeReduceColumn_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h0 → _p2mH0
open _root_.P2MLLL.t0e4be313 renaming h1 → Hex.Internal.LLLState.sizeReduce_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h1 → _p2mH1
open _root_.P2MLLL.t0e4be313 renaming h2 → Hex.Internal.LLLState.swapStep_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h2 → _p2mH2
open _root_.P2MLLL.t0e4be313 renaming h3 → Hex.Internal.lllLoop_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h3 → _p2mH3
open _root_.P2MLLL.t0e4be313 renaming h35 → Hex.Internal.LLLState.sizeReduce_foldl_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h35 → _p2mH35


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t0e4be313 renaming h0 → Hex.Internal.LLLState.sizeReduceColumn_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h0 → _p2mH0
open _root_.P2MLLL.t0e4be313 renaming h1 → Hex.Internal.LLLState.sizeReduce_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h1 → _p2mH1
open _root_.P2MLLL.t0e4be313 renaming h2 → Hex.Internal.LLLState.swapStep_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h2 → _p2mH2
open _root_.P2MLLL.t0e4be313 renaming h3 → Hex.Internal.lllLoop_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h3 → _p2mH3

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section


set_option autoImplicit true



section

/-!
The executable-`Vector` ↔ Mathlib-`Fin n → R` equivalence, the fold-to-`Finset.sum`
bridge for dot products, and the matrix-vector-product correspondence.

These are the base facts through which the row-span, rank, and nullspace bridges
(in `HexRowReduceTheory`) and the lattice bridges (in `HexLLLTheory`) move
between the two vector representations.
-/

open Matrix

namespace HexMatrixTheory

universe u

variable {R : Type u} {n m : Nat}



set_option maxRecDepth 8192
/-- `vectorEquiv v` has entry `v[i]` at `i`, so a caller can rewrite
`vectorEquiv v i` to `v[i]` without unfolding it. -/
@[simp, grind =] theorem _root_.P2MLLL.t0e4be313.h24 (v : Vector R n) (i : Fin n) :
    vectorEquiv v i = v[i] :=
  rfl
open _root_.P2MLLL.t0e4be313 renaming h24 → HexMatrixTheory.vectorEquiv_apply
open _root_.P2MLLL.t0e4be313 renaming h24 → _p2mH24




set_option maxRecDepth 8192
/-- A left fold of `(· + f ·)` over `List.finRange n` from `0` is the finite sum
`∑ i, f i`; the bridge from the executable fold-sum to Mathlib's `Finset.sum`. -/
theorem _root_.P2MLLL.t0e4be313.h23 [AddCommMonoid R] (f : Fin n → R) :
    (List.finRange n).foldl (fun acc i => acc + f i) 0 = ∑ i, f i := by
  rw [← List.foldl_map]
  rw [← List.sum_eq_foldl]
  rw [← List.sum_toFinset f (List.nodup_finRange n)]
  rw [List.toFinset_finRange]
open _root_.P2MLLL.t0e4be313 renaming h23 → HexMatrixTheory.foldl_finRange_eq_sum
open _root_.P2MLLL.t0e4be313 renaming h23 → _p2mH23










end HexMatrixTheory
open _root_.P2MLLL.t0e4be313 renaming h23 → HexMatrixTheory.foldl_finRange_eq_sum
open _root_.P2MLLL.t0e4be313 renaming h23 → _p2mH23
open _root_.P2MLLL.t0e4be313 renaming h24 → HexMatrixTheory.vectorEquiv_apply
open _root_.P2MLLL.t0e4be313 renaming h24 → _p2mH24


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t0e4be313 renaming h23 → HexMatrixTheory.foldl_finRange_eq_sum
open _root_.P2MLLL.t0e4be313 renaming h23 → _p2mH23
open _root_.P2MLLL.t0e4be313 renaming h24 → HexMatrixTheory.vectorEquiv_apply
open _root_.P2MLLL.t0e4be313 renaming h24 → _p2mH24

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section






set_option autoImplicit true



section
set_option maxHeartbeats 1600000

/-!
Rank, row-span, and nullspace correspondence theorems for `hex-matrix-theory`.

This module converts the executable `Hex.Matrix` row-reduction data into
Mathlib's function-based matrix model, then states theorems relating
computed rank, span membership, and nullspace bases to Mathlib's
noncomputable linear-algebra definitions.
-/

namespace HexMatrixTheory

universe u

variable {R : Type u} {n m : Nat}

set_option maxRecDepth 8192
/-- The executable row combination `Hex.Matrix.vecMul c M` (the linear
combination of the rows of `M` with coefficients `c`) transports under
`vectorEquiv` to Mathlib's `Fintype.linearCombination` over the rows of
`matrixEquiv M`. This identifies the computed row span with Mathlib's span. -/
theorem _root_.P2MLLL.t0e4be313.h25 [CommRing R] (M : Hex.Matrix R n m) (c : Vector R n) :
    vectorEquiv (Hex.Matrix.vecMul c M) =
      Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c) := by
  funext j
  simp only [_root_.P2MLLL.t0e4be313.h24]
  unfold Hex.Matrix.vecMul
  change (Hex.Matrix.mulVec (Hex.Matrix.transpose M) c)[j.val] =
    (Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c)) j
  unfold Hex.Matrix.mulVec Hex.Matrix.row Vector.dotProduct Hex.Matrix.transpose
  rw [Hex.Vector.ofFn'_eq_ofFn, Vector.getElem_ofFn j.isLt, _root_.P2MLLL.t0e4be313.h23,
    Fintype.linearCombination_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [_root_.P2MLLL.t0e4be313.h24, matrixEquiv_apply, _root_.Matrix.row_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [mul_comm]
  congr 1
  rw [← Hex.Matrix.getElem_eq_getRow, Hex.Matrix.getElem_ofFn,
    Hex.Matrix.getElem_pair_eq_nested]
open _root_.P2MLLL.t0e4be313 renaming h25 → HexMatrixTheory.vectorEquiv_vecMul
open _root_.P2MLLL.t0e4be313 renaming h25 → _p2mH25






















end HexMatrixTheory
open _root_.P2MLLL.t0e4be313 renaming h25 → HexMatrixTheory.vectorEquiv_vecMul
open _root_.P2MLLL.t0e4be313 renaming h25 → _p2mH25


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t0e4be313 renaming h25 → HexMatrixTheory.vectorEquiv_vecMul
open _root_.P2MLLL.t0e4be313 renaming h25 → _p2mH25

section




set_option autoImplicit true



set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
open scoped BigOperators
variable {n m : Nat}



set_option maxRecDepth 8192
@[simp] theorem _root_.P2MLLL.t0e4be313.h26 (b : Hex.Matrix Int n m) (v : Vector Int m) :
    Hex.Matrix.memLattice (current b) v ↔ Hex.Matrix.memLattice b v := by
  unfold current
  split_ifs with hn
  · exact _root_.P2MLLL.t0e4be313.h3 _ 1 _ _ _ _ hn _ v
  · rfl
open _root_.P2MLLL.t0e4be313 renaming h26 → InfoLossLAR.WorstCase.NativeLLL.current_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h26 → _p2mH26
















end InfoLossLAR.WorstCase.NativeLLL
open _root_.P2MLLL.t0e4be313 renaming h26 → InfoLossLAR.WorstCase.NativeLLL.current_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h26 → _p2mH26


end
open _root_.P2MLLL.t0e4be313 renaming h26 → InfoLossLAR.WorstCase.NativeLLL.current_memLattice_iff
open _root_.P2MLLL.t0e4be313 renaming h26 → _p2mH26

section



set_option autoImplicit true



set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
open scoped BigOperators
variable {n : Nat}

set_option maxRecDepth 8192
theorem _root_.P2MLLL.t0e4be313.h27 (B : Matrix (Fin n) (Fin n) ℤ) : input (basis B) = current (input B) := by
  apply Hex.Matrix.ext_getElem
  intro i j
  simp only [input,Hex.Matrix.getElem_ofFn,basis,Matrix.transpose_apply,
    HexMatrixTheory.matrixEquiv_apply]
open _root_.P2MLLL.t0e4be313 renaming h27 → InfoLossLAR.WorstCase.NativeLLL.input_basis
open _root_.P2MLLL.t0e4be313 renaming h27 → _p2mH27


set_option maxRecDepth 8192
theorem _root_.P2MLLL.t0e4be313.h29 (B : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    Hex.Matrix.vecMul (Vector.ofFn z) (input B) = Vector.ofFn (B.mulVec z) := by
  apply HexMatrixTheory.vectorEquiv.injective
  rw [_root_.P2MLLL.t0e4be313.h25]
  ext row
  simp only [Fintype.linearCombination_apply,Finset.sum_apply,Pi.smul_apply,
    HexMatrixTheory.matrixEquiv_apply,Hex.Matrix.getElem_row,input,
    Hex.Matrix.getElem_ofFn,_root_.P2MLLL.t0e4be313.h24,Vector.getElem_ofFn,
    zsmul_eq_mul,Matrix.row,Pi.mul_apply,Pi.intCast_apply,Fin.getElem_fin,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  change (z j : ℤ)*(Hex.Matrix.ofFn (fun i j => B j i))[j][row] = B row j*z j
  rw [Hex.Matrix.getElem_ofFn]
  exact mul_comm _ _
open _root_.P2MLLL.t0e4be313 renaming h29 → InfoLossLAR.WorstCase.NativeLLL.vecMul_input
open _root_.P2MLLL.t0e4be313 renaming h29 → _p2mH29


set_option maxRecDepth 8192
theorem _root_.P2MLLL.t0e4be313.h28 (B : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    HexLLLTheory.intRowToEuclidean (Hex.Matrix.vecMul (Vector.ofFn z) (input B)) =
      latVec B z := by
  rw [_root_.P2MLLL.t0e4be313.h29]
  ext row
  simp only [HexLLLTheory.intRowToEuclidean,latVec,WithLp.ofLp_toLp,Fin.getElem_fin,Vector.getElem_ofFn]
open _root_.P2MLLL.t0e4be313 renaming h28 → InfoLossLAR.WorstCase.NativeLLL.rowToEuclidean_vecMul_input
open _root_.P2MLLL.t0e4be313 renaming h28 → _p2mH28


set_option maxRecDepth 8192
/-- The logarithmic-budget executable reducer preserves the exact original target lattice. -/
theorem _root_.InfoLossLAR.WorstCase.NativeLLL.__p2m_proof_0e4be3138b79c5a96bbd (B : Matrix (Fin n) (Fin n) ℤ) : lattice (basis B) = lattice B := by
  ext point
  change (∃ z,latVec (basis B) z = point) ↔ ∃ z,latVec B z = point
  constructor
  · rintro ⟨z,rfl⟩
    have hv : Hex.Matrix.memLattice (current (input B))
        (Hex.Matrix.vecMul (Vector.ofFn z) (input (basis B))) := by
      rw [←_root_.P2MLLL.t0e4be313.h27]
      exact ⟨Vector.ofFn z,rfl⟩
    obtain ⟨c,hc⟩ := (_root_.P2MLLL.t0e4be313.h26 (input B) _).mp hv
    refine ⟨HexMatrixTheory.vectorEquiv c,?_⟩
    have hz : Vector.ofFn (HexMatrixTheory.vectorEquiv c) = c :=
      HexMatrixTheory.vectorEquiv.left_inv c
    rw [←_root_.P2MLLL.t0e4be313.h28,←_root_.P2MLLL.t0e4be313.h28,hz,hc]
  · rintro ⟨z,rfl⟩
    have hv : Hex.Matrix.memLattice (current (input B))
        (Hex.Matrix.vecMul (Vector.ofFn z) (input B)) :=
      (_root_.P2MLLL.t0e4be313.h26 (input B) _).mpr ⟨Vector.ofFn z,rfl⟩
    obtain ⟨c,hc⟩ := hv
    refine ⟨HexMatrixTheory.vectorEquiv c,?_⟩
    have hz : Vector.ofFn (HexMatrixTheory.vectorEquiv c) = c :=
      HexMatrixTheory.vectorEquiv.left_inv c
    rw [←_root_.P2MLLL.t0e4be313.h28,←_root_.P2MLLL.t0e4be313.h28,hz,_root_.P2MLLL.t0e4be313.h27,hc]









end InfoLossLAR.WorstCase.NativeLLL
open _root_.P2MLLL.t0e4be313 renaming h27 → InfoLossLAR.WorstCase.NativeLLL.input_basis
open _root_.P2MLLL.t0e4be313 renaming h27 → _p2mH27
open _root_.P2MLLL.t0e4be313 renaming h28 → InfoLossLAR.WorstCase.NativeLLL.rowToEuclidean_vecMul_input
open _root_.P2MLLL.t0e4be313 renaming h28 → _p2mH28
open _root_.P2MLLL.t0e4be313 renaming h29 → InfoLossLAR.WorstCase.NativeLLL.vecMul_input
open _root_.P2MLLL.t0e4be313 renaming h29 → _p2mH29


end
open _root_.P2MLLL.t0e4be313 renaming h27 → InfoLossLAR.WorstCase.NativeLLL.input_basis
open _root_.P2MLLL.t0e4be313 renaming h27 → _p2mH27
open _root_.P2MLLL.t0e4be313 renaming h28 → InfoLossLAR.WorstCase.NativeLLL.rowToEuclidean_vecMul_input
open _root_.P2MLLL.t0e4be313 renaming h28 → _p2mH28
open _root_.P2MLLL.t0e4be313 renaming h29 → InfoLossLAR.WorstCase.NativeLLL.vecMul_input
open _root_.P2MLLL.t0e4be313 renaming h29 → _p2mH29


set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.InfoLossLAR.WorstCase.NativeLLL.__p2m_proof_0e4be3138b79c5a96bbd) := @_root_.InfoLossLAR.WorstCase.NativeLLL.__p2m_proof_0e4be3138b79c5a96bbd
