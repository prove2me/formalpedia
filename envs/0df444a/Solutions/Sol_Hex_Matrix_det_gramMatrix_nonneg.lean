-- Prove2me | solution 1 for Hex.Matrix.det_gramMatrix_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T04:35:59.393545+00:00
-- url     : https://prove2.me/submissions/66548364-cfd2-441a-9136-912bc230a945

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



import Definitions.Def_LARLLL_BareissProgram
import Definitions.Def_LARLLL_DeterminantEnumeration
import Definitions.Def_LARLLL_Foundation01
import Init
import Init.Data.List.Sort.Basic
import Init.Grind.Ring.Field
import Std
import Std.Data.ExtTreeMap.Lemmas

namespace P2MLLL.t19afdfff
end P2MLLL.t19afdfff
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





set_option maxRecDepth 8192
/-- Congruence for a multiplicative fold-product under its factor `f`. -/
theorem _root_.P2MLLL.t19afdfff.h46 [Mul R] (xs : List α) (f g : α → R) (z : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc * f x) z = xs.foldl (fun acc x => acc * g x) z :=
  foldl_congr xs _ _ z fun acc x hx => by rw [h x hx]
open _root_.P2MLLL.t19afdfff renaming h46 → List.foldl_mul_congr
open _root_.P2MLLL.t19afdfff renaming h46 → _p2mH46




/-! # Constant step -/



/-! # Permutation invariance -/

set_option maxRecDepth 8192
/-- An additive fold-sum is invariant under permuting the list. -/
theorem _root_.P2MLLL.t19afdfff.h44 [Lean.Grind.Semiring R] (f : α → R) {xs ys : List α}
    (h : xs.Perm ys) (z : R) :
    xs.foldl (fun acc x => acc + f x) z = ys.foldl (fun acc x => acc + f x) z := by
  induction h generalizing z with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons]; exact ih (z + _)
  | swap x y xs => simp only [List.foldl_cons]; congr 1; grind
  | trans _ _ ih₁ ih₂ => exact (ih₁ z).trans (ih₂ z)
open _root_.P2MLLL.t19afdfff renaming h44 → List.foldl_add_perm
open _root_.P2MLLL.t19afdfff renaming h44 → _p2mH44




section Semiring

variable [Lean.Grind.Semiring R]

/-! # Accumulator extraction -/

set_option maxRecDepth 8192
/-- Pull the running accumulator out of an additive fold-sum, taking the sum
from a `0` start. The additive twin of {name}`foldl_mul_eq_mul_foldl`. -/
theorem _root_.P2MLLL.t19afdfff.h39 (xs : List α) (f : α → R) (z : R) :
    xs.foldl (fun acc x => acc + f x) z
      = z + xs.foldl (fun acc x => acc + f x) 0 :=
  calc xs.foldl (fun acc x => acc + f x) z
      = (xs.map f).foldl (· + ·) z :=
        (List.foldl_map (l := xs) (f := f) (g := (· + ·)) (init := z)).symm
    _ = (xs.map f).foldl (· + ·) (z + 0) := by rw [Lean.Grind.Semiring.add_zero]
    _ = z + (xs.map f).foldl (· + ·) 0 := List.foldl_assoc
    _ = z + xs.foldl (fun acc x => acc + f x) 0 := by
        rw [List.foldl_map (l := xs) (f := f) (g := (· + ·)) (init := 0)]
open _root_.P2MLLL.t19afdfff renaming h39 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t19afdfff renaming h39 → _p2mH39


/-! # All-zero collapse -/



set_option maxRecDepth 8192
/-- An additive fold-sum whose body adds a literal `0` returns the initial
accumulator. -/
theorem _root_.P2MLLL.t19afdfff.h45 (xs : List α) (z : R) :
    xs.foldl (fun acc _ => acc + 0) z = z :=
  foldl_add_eq_self xs (fun _ => 0) z fun _ _ => rfl
open _root_.P2MLLL.t19afdfff renaming h45 → List.foldl_add_zero
open _root_.P2MLLL.t19afdfff renaming h45 → _p2mH45


/-! # Scalar factoring -/



set_option maxRecDepth 8192
/-- Factor a left scalar out of an additive fold-sum started from `0`. -/
theorem _root_.P2MLLL.t19afdfff.h41 (xs : List α) (c : R) (f : α → R) :
    xs.foldl (fun acc x => acc + c * f x) 0 =
      c * xs.foldl (fun acc x => acc + f x) 0 := by
  have hzero : c * 0 = 0 := by grind
  simpa [hzero] using foldl_add_mul_left xs c f 0
open _root_.P2MLLL.t19afdfff renaming h41 → List.foldl_add_mul_left_zero
open _root_.P2MLLL.t19afdfff renaming h41 → _p2mH41


set_option maxRecDepth 8192
/-- Factor a right scalar out of an additive fold-sum (right distributivity,
no commutativity needed). -/
theorem _root_.P2MLLL.t19afdfff.h42 (xs : List α) (f : α → R) (c z : R) :
    xs.foldl (fun acc x => acc + f x) z * c =
      xs.foldl (fun acc x => acc + f x * c) (z * c) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (z := z + f x), show (z + f x) * c = z * c + f x * c by grind]
open _root_.P2MLLL.t19afdfff renaming h42 → List.foldl_add_mul_right
open _root_.P2MLLL.t19afdfff renaming h42 → _p2mH42


end Semiring
open _root_.P2MLLL.t19afdfff renaming h39 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t19afdfff renaming h39 → _p2mH39
open _root_.P2MLLL.t19afdfff renaming h41 → List.foldl_add_mul_left_zero
open _root_.P2MLLL.t19afdfff renaming h41 → _p2mH41
open _root_.P2MLLL.t19afdfff renaming h42 → List.foldl_add_mul_right
open _root_.P2MLLL.t19afdfff renaming h42 → _p2mH42
open _root_.P2MLLL.t19afdfff renaming h45 → List.foldl_add_zero
open _root_.P2MLLL.t19afdfff renaming h45 → _p2mH45


section Ring

variable [Lean.Grind.Ring R]

/-! # Negation -/



end Ring

section Semiring

variable [Lean.Grind.Semiring R]

/-! # Additivity -/







end Semiring

section Ring

variable [Lean.Grind.Ring R]

/-! # Subtraction -/





end Ring

section Semiring

variable [Lean.Grind.Semiring R]

/-! # Fubini -/

set_option maxRecDepth 8192
/-- Sum-swap (Fubini) for nested additive fold-sums. -/
theorem _root_.P2MLLL.t19afdfff.h38 {γ : Type w} (xs : List α) (ys : List γ) (f : α → γ → R) :
    xs.foldl (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 =
      ys.foldl (fun acc y => acc + xs.foldl (fun acc' x => acc' + f x y) 0) 0 := by
  induction xs with
  | nil =>
    simp only [List.foldl_nil]
    exact (_root_.P2MLLL.t19afdfff.h45 ys 0).symm
  | cons x xs ih =>
    have hLHS :
        (x :: xs).foldl
            (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 =
          ys.foldl (fun acc' y => acc' + f x y) 0 +
            xs.foldl
              (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 := by
      simp only [List.foldl_cons]
      rw [_root_.P2MLLL.t19afdfff.h39 xs
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
        rw [_root_.P2MLLL.t19afdfff.h39 xs (fun x' => f x' y) (0 + f x y)]
        grind
      rw [hfun]
      exact foldl_add_add ys (fun y => f x y)
        (fun y => xs.foldl (fun acc' x' => acc' + f x' y) 0)
    rw [hLHS, hRHS, ih]
open _root_.P2MLLL.t19afdfff renaming h38 → List.foldl_add_comm
open _root_.P2MLLL.t19afdfff renaming h38 → _p2mH38


end Semiring
open _root_.P2MLLL.t19afdfff renaming h38 → List.foldl_add_comm
open _root_.P2MLLL.t19afdfff renaming h38 → _p2mH38


section Semiring

variable [Lean.Grind.Semiring R]

set_option maxRecDepth 8192
/-- Factor a right scalar out of an additive fold-sum started from `0`. -/
theorem _root_.P2MLLL.t19afdfff.h43 (xs : List α) (f : α → R) (c : R) :
    xs.foldl (fun acc x => acc + f x * c) 0 =
      xs.foldl (fun acc x => acc + f x) 0 * c := by
  simpa [Lean.Grind.Semiring.zero_mul] using
    (_root_.P2MLLL.t19afdfff.h42 xs f c 0).symm
open _root_.P2MLLL.t19afdfff renaming h43 → List.foldl_add_mul_right_zero
open _root_.P2MLLL.t19afdfff renaming h43 → _p2mH43


end Semiring
open _root_.P2MLLL.t19afdfff renaming h43 → List.foldl_add_mul_right_zero
open _root_.P2MLLL.t19afdfff renaming h43 → _p2mH43


/-! # flatMap -/

set_option maxRecDepth 8192
/-- An additive fold-sum over `xs.flatMap f` equals the fold over `xs` whose
body folds each sublist `f x` into the accumulator. -/
theorem _root_.P2MLLL.t19afdfff.h40 [Add R] {γ : Type w}
    (xs : List α) (f : α → List γ) (g : γ → R) (z : R) :
    (xs.flatMap f).foldl (fun acc x => acc + g x) z =
      xs.foldl (fun acc x => (f x).foldl (fun acc y => acc + g y) acc) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
    exact ih ((f x).foldl (fun acc y => acc + g y) z)
open _root_.P2MLLL.t19afdfff renaming h40 → List.foldl_add_flatMap
open _root_.P2MLLL.t19afdfff renaming h40 → _p2mH40


/-! # Indicator pickout -/



/-! # Monotone bounds (`Nat`) -/









/-! # Multiplicative twins -/



section CommSemiring

variable [Lean.Grind.CommSemiring R]







end CommSemiring

end List
open _root_.P2MLLL.t19afdfff renaming h38 → List.foldl_add_comm
open _root_.P2MLLL.t19afdfff renaming h38 → _p2mH38
open _root_.P2MLLL.t19afdfff renaming h39 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t19afdfff renaming h39 → _p2mH39
open _root_.P2MLLL.t19afdfff renaming h40 → List.foldl_add_flatMap
open _root_.P2MLLL.t19afdfff renaming h40 → _p2mH40
open _root_.P2MLLL.t19afdfff renaming h41 → List.foldl_add_mul_left_zero
open _root_.P2MLLL.t19afdfff renaming h41 → _p2mH41
open _root_.P2MLLL.t19afdfff renaming h42 → List.foldl_add_mul_right
open _root_.P2MLLL.t19afdfff renaming h42 → _p2mH42
open _root_.P2MLLL.t19afdfff renaming h43 → List.foldl_add_mul_right_zero
open _root_.P2MLLL.t19afdfff renaming h43 → _p2mH43
open _root_.P2MLLL.t19afdfff renaming h44 → List.foldl_add_perm
open _root_.P2MLLL.t19afdfff renaming h44 → _p2mH44
open _root_.P2MLLL.t19afdfff renaming h45 → List.foldl_add_zero
open _root_.P2MLLL.t19afdfff renaming h45 → _p2mH45
open _root_.P2MLLL.t19afdfff renaming h46 → List.foldl_mul_congr
open _root_.P2MLLL.t19afdfff renaming h46 → _p2mH46


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t19afdfff renaming h38 → List.foldl_add_comm
open _root_.P2MLLL.t19afdfff renaming h38 → _p2mH38
open _root_.P2MLLL.t19afdfff renaming h39 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t19afdfff renaming h39 → _p2mH39
open _root_.P2MLLL.t19afdfff renaming h40 → List.foldl_add_flatMap
open _root_.P2MLLL.t19afdfff renaming h40 → _p2mH40
open _root_.P2MLLL.t19afdfff renaming h41 → List.foldl_add_mul_left_zero
open _root_.P2MLLL.t19afdfff renaming h41 → _p2mH41
open _root_.P2MLLL.t19afdfff renaming h42 → List.foldl_add_mul_right
open _root_.P2MLLL.t19afdfff renaming h42 → _p2mH42
open _root_.P2MLLL.t19afdfff renaming h43 → List.foldl_add_mul_right_zero
open _root_.P2MLLL.t19afdfff renaming h43 → _p2mH43
open _root_.P2MLLL.t19afdfff renaming h44 → List.foldl_add_perm
open _root_.P2MLLL.t19afdfff renaming h44 → _p2mH44
open _root_.P2MLLL.t19afdfff renaming h45 → List.foldl_add_zero
open _root_.P2MLLL.t19afdfff renaming h45 → _p2mH45
open _root_.P2MLLL.t19afdfff renaming h46 → List.foldl_mul_congr
open _root_.P2MLLL.t19afdfff renaming h46 → _p2mH46

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
/-- Flat row-major indices are injective in the row for a fixed column. -/
 theorem _root_.P2MLLL.t19afdfff.h151 {c : Nat} (hc : c < m) :
    ∀ a b : Fin n, a.val * m + c = b.val * m + c → a = b := by
  intro a b h
  have h1 : (a.val * m + c) / m = a.val := flatIdx_div hc
  have h2 : (b.val * m + c) / m = b.val := flatIdx_div hc
  rw [h, h2] at h1
  exact Fin.ext h1.symm
open _root_.P2MLLL.t19afdfff renaming h151 → Hex.Matrix.flatIdx_row_inj
open _root_.P2MLLL.t19afdfff renaming h151 → _p2mH151


set_option maxRecDepth 8192
/-- Entrywise characterization of `setCol`: the destination column is read from
the replacement function and every other column is read from `M`. -/
@[grind =] theorem _root_.P2MLLL.t19afdfff.h22 (M : Matrix R n m) (dst : Fin m) (v : Fin n → R)
    (r : Fin n) (c : Fin m) :
    (setCol M dst v)[r][c] = if c = dst then v r else M[r][c] := by
  obtain ⟨d⟩ := M
  rw [getElem_eq_getRow, getElem_getRow, getElem_eq_getRow, getElem_getRow]
  show (Fin.foldl n (fun d (i : Fin n) =>
      d.set (i.val * m + dst.val) (v i) (flatIdx_lt i.isLt dst.isLt)) d)[r.val * m + c.val]'_ = _
  rw [Fin.foldl_eq_finRange_foldl]
  by_cases hc : c = dst
  · subst hc
    rw [if_pos rfl]
    exact foldl_set_mem (fun i : Fin n => i.val * m + c.val) v
      (fun i => flatIdx_lt i.isLt c.isLt) (_root_.P2MLLL.t19afdfff.h151 c.isLt)
      (List.finRange n) (nodup_finRange n) d r (List.mem_finRange _)
  · rw [if_neg hc]
    exact foldl_set_ne (fun i : Fin n => i.val * m + dst.val) v
      (fun i => flatIdx_lt i.isLt dst.isLt) (flatIdx_lt r.isLt c.isLt)
      (List.finRange n) d (fun i _ heq => by
        have h1 : (i.val * m + dst.val) % m = dst.val := flatIdx_mod dst.isLt
        have h2 : (r.val * m + c.val) % m = c.val := flatIdx_mod c.isLt
        rw [heq, h2] at h1
        exact hc (Fin.ext h1))
open _root_.P2MLLL.t19afdfff renaming h22 → Hex.Matrix.getElem_setCol
open _root_.P2MLLL.t19afdfff renaming h22 → _p2mH22




















end Matrix
open _root_.P2MLLL.t19afdfff renaming h22 → Hex.Matrix.getElem_setCol
open _root_.P2MLLL.t19afdfff renaming h22 → _p2mH22
open _root_.P2MLLL.t19afdfff renaming h151 → Hex.Matrix.flatIdx_row_inj
open _root_.P2MLLL.t19afdfff renaming h151 → _p2mH151

end Hex
open _root_.P2MLLL.t19afdfff renaming h22 → Hex.Matrix.getElem_setCol
open _root_.P2MLLL.t19afdfff renaming h22 → _p2mH22
open _root_.P2MLLL.t19afdfff renaming h151 → Hex.Matrix.flatIdx_row_inj
open _root_.P2MLLL.t19afdfff renaming h151 → _p2mH151


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t19afdfff renaming h22 → Hex.Matrix.getElem_setCol
open _root_.P2MLLL.t19afdfff renaming h22 → _p2mH22

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section



set_option autoImplicit true



section

/-!
Permutation enumeration and inversion-parity arithmetic for the local
Leibniz determinant.

This module defines `permutationVectors`, the recursive enumeration of the
permutations of `Fin n` as length-`n` vectors, together with `inversionCount`,
which counts the inversions of a permutation written as a list. The bulk of the
file establishes how inversion count behaves under list concatenation and under
swaps: `inversionCount_append` splits a concatenation into the inversions of
each part plus the cross-inversions (`crossInversionCount`), and
`inversionCount_adjacent_swap_parity` / `inversionCount_swap_separated_parity`
show that swapping two distinct entries flips inversion parity. These parity
facts underpin the sign computations used by the determinant.

It also proves that the enumeration is a faithful listing of the symmetric
group: `permutationVectors_complete` (every duplicate-free length-`n` vector is
enumerated) and `permutationVectors_nodup` / `permutationVectors_nodup_list` (no
repeats), via the `raiseFinAbove` / `peelLastVector` last-position recursion and
a handful of determinant-agnostic list and `Fin` helpers reused downstream.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

































/-! # Generic list and `Fin` combinatorics

These determinant-agnostic helpers about folds, `Nodup`, and `insertAt`
support the enumeration completeness and duplicate-freeness proofs below,
and are reused by the Leibniz determinant layer downstream. -/



set_option maxRecDepth 8192
/-- For `i ≤ r < xs.length`, element `r + 1` of `xs.insertIdx i x` is the original
`xs[r]`, since the insertion shifts later entries up by one. -/
 theorem _root_.P2MLLL.t19afdfff.h77 {α : Type u}
    (xs : List α) (x : α) {i r : Nat} (h : i ≤ r) (hr : r < xs.length) :
    (xs.insertIdx i x)[r + 1]'(by
      have hi : i ≤ xs.length := Nat.le_trans h (Nat.le_of_lt hr)
      rw [List.length_insertIdx_of_le_length hi]
      omega) = xs[r] := by
  induction xs generalizing i r with
  | nil =>
      cases hr
  | cons y ys ih =>
      cases i with
      | zero =>
          cases r with
          | zero =>
              simp
          | succ r =>
              simp
      | succ i =>
          cases r with
          | zero =>
              omega
          | succ r =>
              simp only [List.insertIdx, List.getElem_cons_succ]
              exact ih (Nat.succ_le_succ_iff.mp h) (Nat.succ_lt_succ_iff.mp hr)
open _root_.P2MLLL.t19afdfff renaming h77 → Hex.Matrix.list_getElem_insertIdx_succ
open _root_.P2MLLL.t19afdfff renaming h77 → _p2mH77











/-! # Completeness and duplicate-freeness of the enumeration -/





set_option maxRecDepth 8192
/-- Indexing `insertAt x v i` at the raised position `raiseFinAbove i r` recovers
the original entry `v[r]`. -/
 theorem _root_.P2MLLL.t19afdfff.h76 {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) (r : Fin n) :
    (insertAt x v i)[_root_.Hex.Matrix.raiseFinAbove i r] = v[r] := by
  unfold insertAt _root_.Hex.Matrix.raiseFinAbove
  split
  · simpa [Vector.getElem_toList] using
      List.getElem_insertIdx_of_lt (l := v.toList) (x := x) (i := i.val)
        (j := r.val) ‹r.val < i.val› (by
          have hi : i.val ≤ v.toList.length := by
            simpa [Vector.length_toList] using Nat.lt_succ_iff.mp i.isLt
          rw [List.length_insertIdx_of_le_length hi]
          simpa [Vector.length_toList] using Nat.lt_succ_of_lt r.isLt)
  · simpa using
      _root_.P2MLLL.t19afdfff.h77 v.toList x (Nat.le_of_not_gt ‹¬r.val < i.val›)
        (by simp [Vector.length_toList])
open _root_.P2MLLL.t19afdfff renaming h76 → Hex.Matrix.insertAt_get_raiseFinAbove
open _root_.P2MLLL.t19afdfff renaming h76 → _p2mH76


























































end Matrix
open _root_.P2MLLL.t19afdfff renaming h76 → Hex.Matrix.insertAt_get_raiseFinAbove
open _root_.P2MLLL.t19afdfff renaming h76 → _p2mH76
open _root_.P2MLLL.t19afdfff renaming h77 → Hex.Matrix.list_getElem_insertIdx_succ
open _root_.P2MLLL.t19afdfff renaming h77 → _p2mH77

end Hex
open _root_.P2MLLL.t19afdfff renaming h76 → Hex.Matrix.insertAt_get_raiseFinAbove
open _root_.P2MLLL.t19afdfff renaming h76 → _p2mH76
open _root_.P2MLLL.t19afdfff renaming h77 → Hex.Matrix.list_getElem_insertIdx_succ
open _root_.P2MLLL.t19afdfff renaming h77 → _p2mH77


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section








set_option autoImplicit true



section

/-!
Core Leibniz-formula definitions for the dense determinant.

This module defines the determinant `det` of a dense square matrix as the
`permutationVectors`-indexed sum of signed Leibniz terms, built from `detSign`
(the inversion-parity sign of a permutation vector), `detProduct` (the unsigned
diagonal product), and `detTerm` (their product). It records the small base
cases `det_one_by_one`, `det_two_by_two`, and `det_principalSubmatrix_zero`, and
provides the reusable `foldl`-arithmetic toolkit (scalar factoring, additive
splitting, permutation invariance, single-index scaling) plus the
`Fin.castSucc`/`Fin.last` inversion-count lemmas used by the recursive
determinant proofs in the sibling modules.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}






















set_option maxRecDepth 8192
/-- A multiplying left fold from `c * z` equals `c` times the same fold from `z`,
factoring the scalar out to the left. -/
 theorem _root_.P2MLLL.t19afdfff.h105 {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (c : R) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc * f x) (c * z) =
      c * xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← show c * (z * f x) = (c * z) * f x by grind]
      exact ih (z * f x)
open _root_.P2MLLL.t19afdfff renaming h105 → Hex.Matrix.foldl_det_product_mul_left
open _root_.P2MLLL.t19afdfff renaming h105 → _p2mH105


set_option maxRecDepth 8192
/-- When `i ∉ xs`, scaling the factor at index `i` by `c` leaves the multiplying
fold unchanged, since no element of `xs` equals `i`. -/
 theorem _root_.P2MLLL.t19afdfff.h106 {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f : β → R) (z : R) (hnot : i ∉ xs) :
    xs.foldl (fun acc x => acc * if x = i then c * f x else f x) z =
      xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mem_cons, not_or] at hnot
      simp only [List.foldl_cons]
      have hx : x ≠ i := by
        intro hxi
        exact hnot.1 hxi.symm
      rw [if_neg hx]
      exact ih (z * f x) hnot.2
open _root_.P2MLLL.t19afdfff renaming h106 → Hex.Matrix.foldl_det_product_no_scale
open _root_.P2MLLL.t19afdfff renaming h106 → _p2mH106


set_option maxRecDepth 8192
/-- For a `Nodup` list `xs` containing `i`, scaling only the factor at `i` by `c`
multiplies the entire multiplying fold by `c`. -/
 theorem _root_.P2MLLL.t19afdfff.h108 {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f : β → R) (z : R)
    (hmem : i ∈ xs) (hnodup : xs.Nodup) :
    xs.foldl (fun acc x => acc * if x = i then c * f x else f x) z =
      c * xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [if_pos rfl]
        calc
          xs.foldl (fun acc x => acc * if x = i then c * f x else f x) (z * (c * f i)) =
              xs.foldl (fun acc x => acc * f x) (z * (c * f i)) := by
                exact _root_.P2MLLL.t19afdfff.h106 xs i c f (z * (c * f i)) hnodup.1
          _ = xs.foldl (fun acc x => acc * f x) (c * (z * f i)) := by
                congr 1
                grind
          _ = c * xs.foldl (fun acc x => acc * f x) (z * f i) := by
                exact _root_.P2MLLL.t19afdfff.h105 xs c f (z * f i)
      · rw [if_neg hx]
        have hmemTail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        exact ih (z * f x) hmemTail hnodup.2
open _root_.P2MLLL.t19afdfff renaming h108 → Hex.Matrix.foldl_det_product_single_scale
open _root_.P2MLLL.t19afdfff renaming h108 → _p2mH108


set_option maxRecDepth 8192
/-- A multiplying left fold from a sum `a + b` of starting accumulators equals the
sum of the folds from `a` and from `b`. -/
 theorem _root_.P2MLLL.t19afdfff.h104 {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f : β → R) (a b : R) :
    xs.foldl (fun acc x => acc * f x) (a + b) =
      xs.foldl (fun acc x => acc * f x) a +
        xs.foldl (fun acc x => acc * f x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      calc
        xs.foldl (fun acc x => acc * f x) ((a + b) * f x) =
          xs.foldl (fun acc x => acc * f x) (a * f x + b * f x) := by
            congr 1
            grind
        _ =
          xs.foldl (fun acc x => acc * f x) (a * f x) +
            xs.foldl (fun acc x => acc * f x) (b * f x) := by
            exact ih (a * f x) (b * f x)
open _root_.P2MLLL.t19afdfff renaming h104 → Hex.Matrix.foldl_det_product_add_start
open _root_.P2MLLL.t19afdfff renaming h104 → _p2mH104


set_option maxRecDepth 8192
/-- For a `Nodup` list containing `i` with `g` agreeing with `f` away from `i`,
replacing the factor at `i` by `f i + c * g i` splits the fold into the `f`-product
plus `c` times the `g`-product. -/
 theorem _root_.P2MLLL.t19afdfff.h107 {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f g : β → R) (z : R)
    (hmem : i ∈ xs) (hnodup : xs.Nodup)
    (hagree : ∀ x, x ∈ xs → x ≠ i → g x = f x) :
    xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x) z =
      xs.foldl (fun acc x => acc * f x) z +
        c * xs.foldl (fun acc x => acc * g x) z := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [if_pos rfl]
        have hnot : i ∉ xs := hnodup.1
        calc
          xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x)
              (z * (f i + c * g i)) =
            xs.foldl (fun acc x => acc * f x) (z * (f i + c * g i)) := by
              apply _root_.P2MLLL.t19afdfff.h46
              intro y hy
              have hyi : y ≠ i := by
                intro h
                exact hnot (h ▸ hy)
              rw [if_neg hyi]
          _ = xs.foldl (fun acc x => acc * f x) (z * f i + c * (z * g i)) := by
              congr 1
              grind
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              xs.foldl (fun acc x => acc * f x) (c * (z * g i)) := by
              exact _root_.P2MLLL.t19afdfff.h104 xs f (z * f i) (c * (z * g i))
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              c * xs.foldl (fun acc x => acc * f x) (z * g i) := by
              rw [show
                xs.foldl (fun acc x => acc * f x) (c * (z * g i)) =
                  c * xs.foldl (fun acc x => acc * f x) (z * g i) from
                    _root_.P2MLLL.t19afdfff.h105 xs c f (z * g i)]
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              c * xs.foldl (fun acc x => acc * g x) (z * g i) := by
              congr 2
              apply _root_.P2MLLL.t19afdfff.h46
              intro y hy
              exact (hagree y (List.mem_cons.mpr (Or.inr hy)) (by
                intro h
                exact hnot (h ▸ hy))).symm
      · rw [if_neg hx]
        have hmemTail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        have hgx : g x = f x := hagree x (List.mem_cons.mpr (Or.inl rfl)) hx
        calc
          xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x)
              (z * f x) =
            xs.foldl (fun acc x => acc * f x) (z * f x) +
              c * xs.foldl (fun acc x => acc * g x) (z * f x) := by
              exact ih (z * f x) hmemTail hnodup.2
                (fun y hy hyi => hagree y (List.mem_cons.mpr (Or.inr hy)) hyi)
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f x) +
              c * xs.foldl (fun acc x => acc * g x) (z * g x) := by
              rw [hgx]
open _root_.P2MLLL.t19afdfff renaming h107 → Hex.Matrix.foldl_det_product_single_add
open _root_.P2MLLL.t19afdfff renaming h107 → _p2mH107

















set_option maxRecDepth 8192
/-- `inversionCount` is invariant under mapping the permutation list through
`Fin.castSucc`. -/
 theorem _root_.P2MLLL.t19afdfff.h111 {n : Nat} (xs : List (Fin n)) :
    inversionCount (xs.map Fin.castSucc) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [inversionCount, ih, _root_.Hex.Matrix.inversionFold_map_castSucc]
open _root_.P2MLLL.t19afdfff renaming h111 → Hex.Matrix.inversionCount_map_castSucc
open _root_.P2MLLL.t19afdfff renaming h111 → _p2mH111




set_option maxRecDepth 8192
/-- Inserting `Fin.last n` at any position into the `castSucc`-embedded list leaves
the inversion fold against `x.castSucc` unchanged, since the new last element is
never below `x.castSucc`. -/
 theorem _root_.P2MLLL.t19afdfff.h109 {n : Nat} (xs : List (Fin n))
    (x : Fin n) (p acc : Nat) :
    ((xs.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc =
      (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc := by
  induction xs generalizing p acc with
  | nil =>
      cases p <;> simp [List.insertIdx, Fin.lt_def]
  | cons y ys ih =>
      cases p with
      | zero =>
          have hnlt : ¬ n < x.val := by omega
          simp [List.insertIdx, Fin.lt_def, hnlt]
      | succ p =>
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_succ_cons]
          simp only [List.foldl_cons]
          change
            ((ys.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0)
                (acc + if y.castSucc < x.castSucc then 1 else 0) =
              (ys.map Fin.castSucc).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0)
                (acc + if y.castSucc < x.castSucc then 1 else 0)
          rw [ih p (acc + if y.castSucc < x.castSucc then 1 else 0)]
open _root_.P2MLLL.t19afdfff renaming h109 → Hex.Matrix.foldl_insertIdx_last_castSucc_not_lt
open _root_.P2MLLL.t19afdfff renaming h109 → _p2mH109


set_option maxRecDepth 8192
/-- Every `castSucc`-embedded element is below `Fin.last n`, so folding the
`< Fin.last n` count over the embedded list adds exactly its length. -/
 theorem _root_.P2MLLL.t19afdfff.h103 {n : Nat} (xs : List (Fin n)) (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < Fin.last n then 1 else 0) acc =
      acc + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons, List.length_cons]
      rw [ih (acc + if x.castSucc < Fin.last n then 1 else 0)]
      simp [Fin.lt_def]
      omega
open _root_.P2MLLL.t19afdfff renaming h103 → Hex.Matrix.foldl_all_lt_last_castSucc
open _root_.P2MLLL.t19afdfff renaming h103 → _p2mH103


set_option maxRecDepth 8192
/-- Inserting `Fin.last n` at position `p ≤ xs.length` into the `castSucc`-embedded
list raises the inversion count by the `xs.length - p` elements it jumps over. -/
 theorem _root_.P2MLLL.t19afdfff.h110 {n : Nat}
    (xs : List (Fin n)) (p : Nat) (hp : p ≤ xs.length) :
    inversionCount ((xs.map Fin.castSucc).insertIdx p (Fin.last n)) =
      inversionCount xs + (xs.length - p) := by
  induction xs generalizing p with
  | nil =>
      cases p with
      | zero => rfl
      | succ p => cases hp
  | cons x xs ih =>
      cases p with
      | zero =>
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_zero]
          simp only [inversionCount, List.foldl_cons]
          rw [_root_.P2MLLL.t19afdfff.h103 xs
            (0 + if x.castSucc < Fin.last n then 1 else 0)]
          rw [_root_.Hex.Matrix.inversionFold_map_castSucc, _root_.P2MLLL.t19afdfff.h111]
          simp [Fin.lt_def]
          omega
      | succ p =>
          have hp' : p ≤ xs.length := Nat.succ_le_succ_iff.mp hp
          have hlen : (x :: xs).length - (p + 1) = xs.length - p := by
            simp
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_succ_cons]
          simp only [inversionCount]
          change
            ((xs.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0) 0 +
                inversionCount ((xs.map Fin.castSucc).insertIdx p (Fin.last n)) =
              xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
                inversionCount xs + ((x :: xs).length - (p + 1))
          rw [_root_.P2MLLL.t19afdfff.h109 xs x p, _root_.Hex.Matrix.inversionFold_map_castSucc, ih p hp',
            hlen]
          grind
open _root_.P2MLLL.t19afdfff renaming h110 → Hex.Matrix.inversionCount_insertIdx_castSucc_last_eq
open _root_.P2MLLL.t19afdfff renaming h110 → _p2mH110



end Matrix
open _root_.P2MLLL.t19afdfff renaming h103 → Hex.Matrix.foldl_all_lt_last_castSucc
open _root_.P2MLLL.t19afdfff renaming h103 → _p2mH103
open _root_.P2MLLL.t19afdfff renaming h104 → Hex.Matrix.foldl_det_product_add_start
open _root_.P2MLLL.t19afdfff renaming h104 → _p2mH104
open _root_.P2MLLL.t19afdfff renaming h105 → Hex.Matrix.foldl_det_product_mul_left
open _root_.P2MLLL.t19afdfff renaming h105 → _p2mH105
open _root_.P2MLLL.t19afdfff renaming h106 → Hex.Matrix.foldl_det_product_no_scale
open _root_.P2MLLL.t19afdfff renaming h106 → _p2mH106
open _root_.P2MLLL.t19afdfff renaming h107 → Hex.Matrix.foldl_det_product_single_add
open _root_.P2MLLL.t19afdfff renaming h107 → _p2mH107
open _root_.P2MLLL.t19afdfff renaming h108 → Hex.Matrix.foldl_det_product_single_scale
open _root_.P2MLLL.t19afdfff renaming h108 → _p2mH108
open _root_.P2MLLL.t19afdfff renaming h109 → Hex.Matrix.foldl_insertIdx_last_castSucc_not_lt
open _root_.P2MLLL.t19afdfff renaming h109 → _p2mH109
open _root_.P2MLLL.t19afdfff renaming h110 → Hex.Matrix.inversionCount_insertIdx_castSucc_last_eq
open _root_.P2MLLL.t19afdfff renaming h110 → _p2mH110
open _root_.P2MLLL.t19afdfff renaming h111 → Hex.Matrix.inversionCount_map_castSucc
open _root_.P2MLLL.t19afdfff renaming h111 → _p2mH111

end Hex
open _root_.P2MLLL.t19afdfff renaming h103 → Hex.Matrix.foldl_all_lt_last_castSucc
open _root_.P2MLLL.t19afdfff renaming h103 → _p2mH103
open _root_.P2MLLL.t19afdfff renaming h104 → Hex.Matrix.foldl_det_product_add_start
open _root_.P2MLLL.t19afdfff renaming h104 → _p2mH104
open _root_.P2MLLL.t19afdfff renaming h105 → Hex.Matrix.foldl_det_product_mul_left
open _root_.P2MLLL.t19afdfff renaming h105 → _p2mH105
open _root_.P2MLLL.t19afdfff renaming h106 → Hex.Matrix.foldl_det_product_no_scale
open _root_.P2MLLL.t19afdfff renaming h106 → _p2mH106
open _root_.P2MLLL.t19afdfff renaming h107 → Hex.Matrix.foldl_det_product_single_add
open _root_.P2MLLL.t19afdfff renaming h107 → _p2mH107
open _root_.P2MLLL.t19afdfff renaming h108 → Hex.Matrix.foldl_det_product_single_scale
open _root_.P2MLLL.t19afdfff renaming h108 → _p2mH108
open _root_.P2MLLL.t19afdfff renaming h109 → Hex.Matrix.foldl_insertIdx_last_castSucc_not_lt
open _root_.P2MLLL.t19afdfff renaming h109 → _p2mH109
open _root_.P2MLLL.t19afdfff renaming h110 → Hex.Matrix.inversionCount_insertIdx_castSucc_last_eq
open _root_.P2MLLL.t19afdfff renaming h110 → _p2mH110
open _root_.P2MLLL.t19afdfff renaming h111 → Hex.Matrix.inversionCount_map_castSucc
open _root_.P2MLLL.t19afdfff renaming h111 → _p2mH111


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section



set_option autoImplicit true



section

/-!
Permutation-group structure on permutation vectors.

This module develops the operations on permutation vectors that the elementary
row and column operation laws are built from: `finTranspose` and
`transposePermutationValues`/`swapPermutationValues` (position and value swaps),
`inversePermutationVector`, and `composePermutationValues`. It shows these
preserve membership in `permutationVectors` and tracks their effect on inversion
parity, culminating in `detSign_swapPermutationValues` and the multiplicativity
law `detSign_composePermutationValues`. The elementary-operation determinant
laws themselves live in `HexDeterminant.RowOps`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}









set_option maxRecDepth 8192
/-- `finTranspose i j` is an involution: applying it twice returns `r`. -/
 theorem _root_.P2MLLL.t19afdfff.h123 {n : Nat} (i j r : Fin n) :
    finTranspose i j (finTranspose i j r) = r := by
  by_cases hi : r = i
  · subst r
    rw [_root_.Hex.Matrix.finTranspose_left, _root_.Hex.Matrix.finTranspose_right]
  · by_cases hj : r = j
    · subst r
      rw [_root_.Hex.Matrix.finTranspose_right, _root_.Hex.Matrix.finTranspose_left]
    · rw [_root_.Hex.Matrix.finTranspose_of_ne i j r hi hj]
      exact _root_.Hex.Matrix.finTranspose_of_ne i j r hi hj
open _root_.P2MLLL.t19afdfff renaming h123 → Hex.Matrix.finTranspose_involutive
open _root_.P2MLLL.t19afdfff renaming h123 → _p2mH123


set_option maxRecDepth 8192
/-- `finTranspose i j` is injective, since it is its own inverse. -/
 theorem _root_.P2MLLL.t19afdfff.h122 {n : Nat} (i j : Fin n) :
    Function.Injective (finTranspose i j) := by
  intro a b h
  have h' := congrArg (finTranspose i j) h
  simpa [_root_.P2MLLL.t19afdfff.h123] using h'
open _root_.P2MLLL.t19afdfff renaming h122 → Hex.Matrix.finTranspose_injective
open _root_.P2MLLL.t19afdfff renaming h122 → _p2mH122


set_option maxRecDepth 8192
/-- Mapping `finTranspose i j` over `List.finRange n` permutes it, since the
transposition is a bijection of `Fin n`. -/
 theorem _root_.P2MLLL.t19afdfff.h121 {n : Nat} (i j : Fin n) :
    ((List.finRange n).map (finTranspose i j)).Perm (List.finRange n) := by
  apply (List.perm_ext_iff_of_nodup
    (_root_.Hex.Matrix.list_nodup_map_of_injective (_root_.P2MLLL.t19afdfff.h122 i j) (List.nodup_finRange n))
    (List.nodup_finRange n)).mpr
  intro r
  constructor
  · intro _h
    exact List.mem_finRange r
  · intro _h
    simp only [List.mem_map]
    exact ⟨finTranspose i j r, List.mem_finRange _, by
      rw [_root_.P2MLLL.t19afdfff.h123]⟩
open _root_.P2MLLL.t19afdfff renaming h121 → Hex.Matrix.finRange_map_finTranspose_perm
open _root_.P2MLLL.t19afdfff renaming h121 → _p2mH121










set_option maxRecDepth 8192
/-- `vector_toList_eq` rewrites a vector's list view as the finite range of indices mapped through its getter. -/
 theorem _root_.P2MLLL.t19afdfff.h141 {α : Type u} {n : Nat}
    (v : Vector α n) :
    v.toList = (List.finRange n).map fun i => v[i] := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp
open _root_.P2MLLL.t19afdfff renaming h141 → Hex.Matrix.vector_toList_eq
open _root_.P2MLLL.t19afdfff renaming h141 → _p2mH141


set_option maxRecDepth 8192
/-- `transposePermutationValues_toList_perm` shows that transposing two positions in a permutation vector only permutes its list of values. -/
 theorem _root_.P2MLLL.t19afdfff.h140 {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    (_root_.Hex.Matrix.transposePermutationValues perm i j).toList.Perm perm.toList := by
  rw [_root_.P2MLLL.t19afdfff.h141 (_root_.Hex.Matrix.transposePermutationValues perm i j), _root_.P2MLLL.t19afdfff.h141 perm]
  have hleft :
      (List.finRange n).map (fun r => (_root_.Hex.Matrix.transposePermutationValues perm i j)[r]) =
        (List.finRange n).map ((fun r => perm[r]) ∘ finTranspose i j) := by
    apply List.map_congr_left
    intro r _hr
    exact _root_.Hex.Matrix.transposePermutationValues_get perm i j r
  rw [hleft]
  simpa [List.map_map] using
    (_root_.P2MLLL.t19afdfff.h121 i j).map fun r => perm[r]
open _root_.P2MLLL.t19afdfff renaming h140 → Hex.Matrix.transposePermutationValues_toList_perm
open _root_.P2MLLL.t19afdfff renaming h140 → _p2mH140


set_option maxRecDepth 8192
/-- `transposePermutationValues_mem_permutationVectors` preserves membership in `permutationVectors n` after transposing two positions. -/
 theorem _root_.P2MLLL.t19afdfff.h139 {n : Nat}
    {perm : Vector (Fin n) n} (i j : Fin n)
    (hmem : perm ∈ permutationVectors n) :
    _root_.Hex.Matrix.transposePermutationValues perm i j ∈ permutationVectors n := by
  apply permutationVectors_complete
  exact (_root_.P2MLLL.t19afdfff.h140 perm i j).symm.nodup
    (permutationVectors_nodup hmem)
open _root_.P2MLLL.t19afdfff renaming h139 → Hex.Matrix.transposePermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h139 → _p2mH139


























set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h138 {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.Nodup := by
  change (perm.map (finTranspose i j)).toList.Nodup
  rw [vector_toList_map]
  exact _root_.Hex.Matrix.list_nodup_map_of_injective (_root_.P2MLLL.t19afdfff.h122 i j) hnodup
open _root_.P2MLLL.t19afdfff renaming h138 → Hex.Matrix.swapPermutationValues_toList_nodup
open _root_.P2MLLL.t19afdfff renaming h138 → _p2mH138


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h137 {n : Nat}
    {perm : Vector (Fin n) n} (i j : Fin n)
    (hmem : perm ∈ permutationVectors n) :
    swapPermutationValues perm i j ∈ permutationVectors n := by
  apply permutationVectors_complete
  exact _root_.P2MLLL.t19afdfff.h138 perm i j (permutationVectors_nodup hmem)
open _root_.P2MLLL.t19afdfff renaming h137 → Hex.Matrix.swapPermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h137 → _p2mH137


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h136 {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    swapPermutationValues (swapPermutationValues perm i j) i j = perm := by
  ext r hr
  simp [swapPermutationValues, _root_.P2MLLL.t19afdfff.h123]
open _root_.P2MLLL.t19afdfff renaming h136 → Hex.Matrix.swapPermutationValues_involutive
open _root_.P2MLLL.t19afdfff renaming h136 → _p2mH136








set_option maxRecDepth 8192
/-- `inversePermutationValues_get_value` is the right-inverse law
`perm[inv[c]] = c`, recovering the value `c` by reading `perm` at the position
the inverse records for it. -/
 theorem _root_.P2MLLL.t19afdfff.h125 {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) (c : Fin n) :
    perm[(inversePermutationValues perm hnodup)[c]] = c := by
  change
    perm.toList[(inversePermutationValues perm hnodup)[c].val]'(by
      simp [Vector.length_toList]) = c
  simp [inversePermutationValues]
open _root_.P2MLLL.t19afdfff renaming h125 → Hex.Matrix.inversePermutationValues_get_value
open _root_.P2MLLL.t19afdfff renaming h125 → _p2mH125


set_option maxRecDepth 8192
/-- `inversePermutationValues_get_index` is the left-inverse law
`inv[perm[i]] = i`, recovering the position `i` from the value `perm` places
there. -/
 theorem _root_.P2MLLL.t19afdfff.h124 {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) (i : Fin n) :
    (inversePermutationValues perm hnodup)[perm[i]] = i := by
  apply Fin.ext
  simp [inversePermutationValues]
  exact hnodup.idxOf_getElem i.val (by simp [Vector.length_toList])
open _root_.P2MLLL.t19afdfff renaming h124 → Hex.Matrix.inversePermutationValues_get_index
open _root_.P2MLLL.t19afdfff renaming h124 → _p2mH124


set_option maxRecDepth 8192
/-- `inversePermutationValues_nodup` shows the inverse permutation vector is
itself nodup, so it is again a valid permutation usable in the determinant
sign-tracking expansion. -/
 theorem _root_.P2MLLL.t19afdfff.h128 {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    (inversePermutationValues perm hnodup).toList.Nodup := by
  rw [_root_.P2MLLL.t19afdfff.h141]
  apply _root_.Hex.Matrix.list_nodup_map_of_injective
  · intro a b h
    have hval :
        perm[(inversePermutationValues perm hnodup)[a]] =
          perm[(inversePermutationValues perm hnodup)[b]] :=
      congrArg (fun k => perm[k]) h
    rw [_root_.P2MLLL.t19afdfff.h125 perm hnodup a] at hval
    rw [_root_.P2MLLL.t19afdfff.h125 perm hnodup b] at hval
    exact hval
  · exact List.nodup_finRange n
open _root_.P2MLLL.t19afdfff renaming h128 → Hex.Matrix.inversePermutationValues_nodup
open _root_.P2MLLL.t19afdfff renaming h128 → _p2mH128










set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h127 {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationValues perm (permutationVectors_nodup hmem) ∈ permutationVectors n := by
  exact permutationVectors_complete
    (_root_.P2MLLL.t19afdfff.h128 perm (permutationVectors_nodup hmem))
open _root_.P2MLLL.t19afdfff renaming h127 → Hex.Matrix.inversePermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h127 → _p2mH127


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h126 {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversePermutationValues
        (inversePermutationValues perm hnodup)
        (_root_.P2MLLL.t19afdfff.h128 perm hnodup) = perm := by
  ext k hk
  apply Fin.val_eq_of_eq
  let i : Fin n := ⟨k, hk⟩
  have h :=
    _root_.P2MLLL.t19afdfff.h124
      (inversePermutationValues perm hnodup)
      (_root_.P2MLLL.t19afdfff.h128 perm hnodup) (perm[i])
  have hi := _root_.P2MLLL.t19afdfff.h124 perm hnodup i
  have hleft :
      (inversePermutationValues
        (inversePermutationValues perm hnodup)
        (_root_.P2MLLL.t19afdfff.h128 perm hnodup))[i] =
        (inversePermutationValues
          (inversePermutationValues perm hnodup)
          (_root_.P2MLLL.t19afdfff.h128 perm hnodup))[
            (inversePermutationValues perm hnodup)[perm[i]]] :=
    congrArg
      (fun x =>
        (inversePermutationValues
          (inversePermutationValues perm hnodup)
          (_root_.P2MLLL.t19afdfff.h128 perm hnodup))[x])
      hi.symm
  exact hleft.trans h
open _root_.P2MLLL.t19afdfff renaming h126 → Hex.Matrix.inversePermutationValues_involutive
open _root_.P2MLLL.t19afdfff renaming h126 → _p2mH126




set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h129 {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversePermutationVector perm = inversePermutationValues perm hnodup := by
  simp [inversePermutationVector, hnodup]
open _root_.P2MLLL.t19afdfff renaming h129 → Hex.Matrix.inversePermutationVector_eq
open _root_.P2MLLL.t19afdfff renaming h129 → _p2mH129


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h131 {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationVector perm ∈ permutationVectors n := by
  rw [_root_.P2MLLL.t19afdfff.h129 perm (permutationVectors_nodup hmem)]
  exact _root_.P2MLLL.t19afdfff.h127 hmem
open _root_.P2MLLL.t19afdfff renaming h131 → Hex.Matrix.inversePermutationVector_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h131 → _p2mH131


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h130 {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationVector (inversePermutationVector perm) = perm := by
  rw [_root_.P2MLLL.t19afdfff.h129 perm (permutationVectors_nodup hmem)]
  rw [_root_.P2MLLL.t19afdfff.h129
    (inversePermutationValues perm (permutationVectors_nodup hmem))
    (_root_.P2MLLL.t19afdfff.h128 perm (permutationVectors_nodup hmem))]
  exact _root_.P2MLLL.t19afdfff.h126 perm (permutationVectors_nodup hmem)
open _root_.P2MLLL.t19afdfff renaming h130 → Hex.Matrix.inversePermutationVector_involutive_of_mem
open _root_.P2MLLL.t19afdfff renaming h130 → _p2mH130




set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h112 {n : Nat}
    (sigma tau : Vector (Fin n) n) (i : Fin n) :
    (composePermutationValues sigma tau)[i] = sigma[tau[i]] := by
  simp [composePermutationValues]
open _root_.P2MLLL.t19afdfff renaming h112 → Hex.Matrix.composePermutationValues_get
open _root_.P2MLLL.t19afdfff renaming h112 → _p2mH112


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h117 {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma.toList.Nodup) (htau : tau.toList.Nodup) :
    (composePermutationValues sigma tau).toList.Nodup := by
  rw [_root_.P2MLLL.t19afdfff.h141 (composePermutationValues sigma tau)]
  apply _root_.Hex.Matrix.list_nodup_map_of_injective
    (f := fun i : Fin n => (composePermutationValues sigma tau)[i])
    ?_ (List.nodup_finRange n)
  intro i j hij
  have hsigma_inj :
      Function.Injective (fun k : Fin n => sigma[k]) := by
    intro a b hab
    have ha_idx :
        sigma.toList.idxOf sigma[a] = a.val := by
      have ha_len : a.val < sigma.toList.length := by
        simp [Vector.length_toList]
      have hget : sigma.toList[a.val] = sigma[a] := by
        simp [Vector.toList]
      simpa [hget] using hsigma.idxOf_getElem a.val ha_len
    have hb_idx :
        sigma.toList.idxOf sigma[b] = b.val := by
      have hb_len : b.val < sigma.toList.length := by
        simp [Vector.length_toList]
      have hget : sigma.toList[b.val] = sigma[b] := by
        simp [Vector.toList]
      simpa [hget] using hsigma.idxOf_getElem b.val hb_len
    apply Fin.ext
    change sigma[a] = sigma[b] at hab
    rw [← ha_idx, ← hb_idx, hab]
  have htau_inj :
      Function.Injective (fun k : Fin n => tau[k]) := by
    intro a b hab
    have ha_idx :
        tau.toList.idxOf tau[a] = a.val := by
      have ha_len : a.val < tau.toList.length := by
        simp [Vector.length_toList]
      have hget : tau.toList[a.val] = tau[a] := by
        simp [Vector.toList]
      simpa [hget] using htau.idxOf_getElem a.val ha_len
    have hb_idx :
        tau.toList.idxOf tau[b] = b.val := by
      have hb_len : b.val < tau.toList.length := by
        simp [Vector.length_toList]
      have hget : tau.toList[b.val] = tau[b] := by
        simp [Vector.toList]
      simpa [hget] using htau.idxOf_getElem b.val hb_len
    apply Fin.ext
    change tau[a] = tau[b] at hab
    rw [← ha_idx, ← hb_idx, hab]
  exact htau_inj (hsigma_inj (by simpa [composePermutationValues] using hij))
open _root_.P2MLLL.t19afdfff renaming h117 → Hex.Matrix.composePermutationValues_nodup
open _root_.P2MLLL.t19afdfff renaming h117 → _p2mH117


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h116 {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma ∈ permutationVectors n)
    (htau : tau ∈ permutationVectors n) :
    composePermutationValues sigma tau ∈ permutationVectors n := by
  exact permutationVectors_complete
    (_root_.P2MLLL.t19afdfff.h117
      (permutationVectors_nodup hsigma) (permutationVectors_nodup htau))
open _root_.P2MLLL.t19afdfff renaming h116 → Hex.Matrix.composePermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h116 → _p2mH116


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h114 {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma ∈ permutationVectors n) :
    composePermutationValues
        (inversePermutationVector sigma)
        (composePermutationValues sigma tau) = tau := by
  ext k hk
  apply Fin.val_eq_of_eq
  let i : Fin n := ⟨k, hk⟩
  change
    (composePermutationValues
        (inversePermutationVector sigma)
        (composePermutationValues sigma tau))[i] = tau[i]
  have hnodup := permutationVectors_nodup hsigma
  rw [_root_.P2MLLL.t19afdfff.h129 sigma hnodup]
  simpa [composePermutationValues] using
    _root_.P2MLLL.t19afdfff.h124 sigma hnodup tau[i]
open _root_.P2MLLL.t19afdfff renaming h114 → Hex.Matrix.composePermutationValues_left_involutive
open _root_.P2MLLL.t19afdfff renaming h114 → _p2mH114


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h113 {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma ∈ permutationVectors n) :
    composePermutationValues sigma
        (composePermutationValues (inversePermutationVector sigma) tau) = tau := by
  have h :=
    _root_.P2MLLL.t19afdfff.h114
      (sigma := inversePermutationVector sigma) (tau := tau)
      (_root_.P2MLLL.t19afdfff.h131 hsigma)
  rw [_root_.P2MLLL.t19afdfff.h130 hsigma] at h
  exact h
open _root_.P2MLLL.t19afdfff renaming h113 → Hex.Matrix.composePermutationValues_left_inverse
open _root_.P2MLLL.t19afdfff renaming h113 → _p2mH113


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h115 {n : Nat}
    (sigma : Vector (Fin n) n) (hsigma : sigma ∈ permutationVectors n) :
    ((permutationVectors n).map fun tau => composePermutationValues sigma tau).Perm
      (permutationVectors n) := by
  have hmapNodup :
      ((permutationVectors n).map fun tau => composePermutationValues sigma tau).Nodup := by
    exact _root_.Hex.Matrix.list_nodup_map_on permutationVectors_nodup_list (by
      intro a ha b hb hab
      have h' := congrArg
        (fun perm => composePermutationValues (inversePermutationVector sigma) perm) hab
      exact
        (_root_.P2MLLL.t19afdfff.h114 (sigma := sigma) (tau := a) hsigma).symm.trans
          (h'.trans
            (_root_.P2MLLL.t19afdfff.h114 (sigma := sigma) (tau := b) hsigma)))
  apply (List.perm_ext_iff_of_nodup hmapNodup permutationVectors_nodup_list).mpr
  intro perm
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨pre, hpre, rfl⟩
    exact _root_.P2MLLL.t19afdfff.h116 hsigma hpre
  · intro hmem
    apply List.mem_map.mpr
    refine ⟨composePermutationValues (inversePermutationVector sigma) perm,
      ?_, ?_⟩
    · exact _root_.P2MLLL.t19afdfff.h116
        (_root_.P2MLLL.t19afdfff.h131 hsigma) hmem
    · exact _root_.P2MLLL.t19afdfff.h113 hsigma
open _root_.P2MLLL.t19afdfff renaming h115 → Hex.Matrix.composePermutationValues_left_map_permutationVectors_perm
open _root_.P2MLLL.t19afdfff renaming h115 → _p2mH115






set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h135 {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (sigma : Vector (Fin n) n) (hsigma : sigma ∈ permutationVectors n)
    (f : Vector (Fin n) n → R) :
    (permutationVectors n).foldl
        (fun acc perm => acc + f (composePermutationValues sigma perm)) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + f (composePermutationValues sigma perm)) 0 =
      ((permutationVectors n).map fun perm => composePermutationValues sigma perm).foldl
        (fun acc perm => acc + f perm) 0 := by
        simp [List.foldl_map]
    _ = (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
        exact _root_.P2MLLL.t19afdfff.h44 f
          (_root_.P2MLLL.t19afdfff.h115 sigma hsigma) 0
open _root_.P2MLLL.t19afdfff renaming h135 → Hex.Matrix.permutationVectors_composePermutationValues_left_sum
open _root_.P2MLLL.t19afdfff renaming h135 → _p2mH135




set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h119 {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (sigma tau : Vector (Fin n) n) :
    detProduct (ofFn fun r c => M[r][sigma[c]]) tau =
      detProduct M (composePermutationValues sigma tau) := by
  unfold detProduct
  simp only [Fin.foldl_eq_finRange_foldl]
  apply _root_.P2MLLL.t19afdfff.h46
  intro r _hr
  simp only [getElem_pair_eq_nested, getElem_ofFn, _root_.P2MLLL.t19afdfff.h112]
open _root_.P2MLLL.t19afdfff renaming h119 → Hex.Matrix.detProduct_colPermute_vector
open _root_.P2MLLL.t19afdfff renaming h119 → _p2mH119














set_option maxRecDepth 8192
/-- An adjacent swap at a descent strictly decreases inversion count by 1. -/
 theorem _root_.P2MLLL.t19afdfff.h132 {n : Nat}
    (pre post : List (Fin n)) (a b : Fin n) (hba : b < a) :
    inversionCount (pre ++ a :: b :: post) =
      inversionCount (pre ++ b :: a :: post) + 1 := by
  rw [show pre ++ a :: b :: post = pre ++ ([a, b] ++ post) by simp,
    show pre ++ b :: a :: post = pre ++ ([b, a] ++ post) by simp]
  have hcross :
      _root_.Hex.Matrix.crossInversionCount pre ([a, b] ++ post) =
        _root_.Hex.Matrix.crossInversionCount pre ([b, a] ++ post) := by
    repeat rw [_root_.Hex.Matrix.crossInversionCount_append_right]
    rw [_root_.Hex.Matrix.crossInversionCount_pair_swap_right]
  have htail :
      _root_.Hex.Matrix.crossInversionCount [a, b] post =
        _root_.Hex.Matrix.crossInversionCount [b, a] post :=
    _root_.Hex.Matrix.crossInversionCount_pair_swap_left post a b
  rw [_root_.Hex.Matrix.inversionCount_append pre ([a, b] ++ post), _root_.Hex.Matrix.inversionCount_append pre ([b, a] ++ post),
    hcross, _root_.Hex.Matrix.inversionCount_append [a, b] post, _root_.Hex.Matrix.inversionCount_append [b, a] post, htail,
    _root_.Hex.Matrix.inversionCount_pair a b, _root_.Hex.Matrix.inversionCount_pair b a]
  have hab' : ¬ a < b := by omega
  simp [hba, hab']
  omega
open _root_.P2MLLL.t19afdfff renaming h132 → Hex.Matrix.inversionCount_adjacent_swap_descent
open _root_.P2MLLL.t19afdfff renaming h132 → _p2mH132


set_option maxRecDepth 8192
/-- For an adjacent descent pair in a permutation vector, transposing the two
positions decreases the inversion count by exactly one. -/
 theorem _root_.P2MLLL.t19afdfff.h133
    {n : Nat} (perm : Vector (Fin n) n)
    {i j : Fin n} (hij : i.val + 1 = j.val) (hdesc : perm[j] < perm[i]) :
    inversionCount perm.toList =
      inversionCount (_root_.Hex.Matrix.transposePermutationValues perm i j).toList + 1 := by
  have hlt : i.val < j.val := by omega
  have hmid : j.val - i.val - 1 = 0 := by omega
  rw [_root_.Hex.Matrix.vector_toList_split_two perm hlt, hmid,
      _root_.Hex.Matrix.transposePermutationValues_toList_of_lt perm hlt, hmid]
  simp only [List.take_zero]
  -- After simplification, both lists have the form `pre ++ x :: y :: post`,
  -- and we apply the strict-decrease lemma.
  have h := _root_.P2MLLL.t19afdfff.h132
    (perm.toList.take i.val) (perm.toList.drop (j.val + 1))
    perm[i] perm[j] hdesc
  simpa using h
open _root_.P2MLLL.t19afdfff renaming h133 → Hex.Matrix.inversionCount_transposePermutationValues_adjacent_descent
open _root_.P2MLLL.t19afdfff renaming h133 → _p2mH133


set_option maxRecDepth 8192
/-- Composition distributes over right transposition of positions. -/
 theorem _root_.P2MLLL.t19afdfff.h118
    {n : Nat} (sigma tau : Vector (Fin n) n) (i j : Fin n) :
    composePermutationValues sigma (_root_.Hex.Matrix.transposePermutationValues tau i j) =
      _root_.Hex.Matrix.transposePermutationValues (composePermutationValues sigma tau) i j := by
  ext k hk
  apply Fin.val_eq_of_eq
  let r : Fin n := ⟨k, hk⟩
  show
    (composePermutationValues sigma (_root_.Hex.Matrix.transposePermutationValues tau i j))[r] =
      (_root_.Hex.Matrix.transposePermutationValues (composePermutationValues sigma tau) i j)[r]
  have h1 : (composePermutationValues sigma (_root_.Hex.Matrix.transposePermutationValues tau i j))[r] =
      sigma[(_root_.Hex.Matrix.transposePermutationValues tau i j)[r]] :=
    _root_.P2MLLL.t19afdfff.h112 sigma (_root_.Hex.Matrix.transposePermutationValues tau i j) r
  have h2 : (_root_.Hex.Matrix.transposePermutationValues tau i j)[r] = tau[finTranspose i j r] :=
    _root_.Hex.Matrix.transposePermutationValues_get tau i j r
  have h3 : (_root_.Hex.Matrix.transposePermutationValues (composePermutationValues sigma tau) i j)[r] =
      (composePermutationValues sigma tau)[finTranspose i j r] :=
    _root_.Hex.Matrix.transposePermutationValues_get (composePermutationValues sigma tau) i j r
  have h4 : (composePermutationValues sigma tau)[finTranspose i j r] =
      sigma[tau[finTranspose i j r]] :=
    _root_.P2MLLL.t19afdfff.h112 sigma tau (finTranspose i j r)
  rw [h1, h3, h4]
  exact congrArg (fun x => sigma[x]) h2
open _root_.P2MLLL.t19afdfff renaming h118 → Hex.Matrix.composePermutationValues_transposePermutationValues_right
open _root_.P2MLLL.t19afdfff renaming h118 → _p2mH118


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h120 {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup)
    (hpos : 0 < inversionCount perm.toList) :
    ∃ i : Fin n, ∃ hij : i.val + 1 < n,
      perm[(⟨i.val + 1, hij⟩ : Fin n)] < perm[i] := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      simp [hnil, inversionCount] at hpos
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          _root_.Hex.Matrix.finLast_idxOf_lt (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := _root_.Hex.Matrix.peelLastVector perm k hk hidx hnodup
      have hpeeled_nodup : peeled.toList.Nodup :=
        _root_.Hex.Matrix.peelLastVector_nodup perm k hk hidx hnodup
      let pos : Fin (n + 1) := ⟨k, hk⟩
      have hinsert :
          insertAt (Fin.last n) (peeled.map Fin.castSucc) pos = perm := by
        simpa [peeled, pos] using
          _root_.Hex.Matrix.insertAt_peelLastVector perm k hk hidx hnodup
      have hcount :
          inversionCount perm.toList =
            inversionCount peeled.toList + (n - pos.val) := by
        rw [← hinsert, insertAt_toList, vector_toList_map]
        simpa [peeled, pos, Vector.length_toList] using
          _root_.P2MLLL.t19afdfff.h110 peeled.toList pos.val (by
            simp [Vector.length_toList, pos]
            omega)
      by_cases hlast : pos.val = n
      · have hpeeled_pos : 0 < inversionCount peeled.toList := by
          rw [hcount] at hpos
          omega
        rcases ih peeled hpeeled_nodup hpeeled_pos with ⟨i, hij, hdesc⟩
        have hijSucc : i.val + 1 < n + 1 := by omega
        let iUp : Fin (n + 1) := ⟨i.val, by omega⟩
        have hijUp : iUp.val + 1 < n + 1 := by simp [iUp, hijSucc]
        refine ⟨iUp, hijUp, ?_⟩
        · have hpos_eq : pos = Fin.last n := Fin.ext hlast
          have hget_next :
              perm[(⟨i.val + 1, hijSucc⟩ : Fin (n + 1))] =
                (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc := by
            have hraw :
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[
                    (⟨i.val + 1, hijSucc⟩ : Fin (n + 1))] =
                  (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc := by
              have hraise :
                  _root_.Hex.Matrix.raiseFinAbove (Fin.last n) (⟨i.val + 1, hij⟩ : Fin n) =
                    (⟨i.val + 1, hijSucc⟩ : Fin (n + 1)) := by
                apply Fin.ext
                simp [_root_.Hex.Matrix.raiseFinAbove, hij]
              have hbase := _root_.P2MLLL.t19afdfff.h76
                (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n)
                (⟨i.val + 1, hij⟩ : Fin n)
              have hbase' :
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[
                      _root_.Hex.Matrix.raiseFinAbove (Fin.last n) (⟨i.val + 1, hij⟩ : Fin n)] =
                    (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc := by
                simpa using hbase
              exact (_root_.Hex.Matrix.vector_get_fin_congr
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))
                hraise).symm.trans hbase'
            have hinsert_last :
                insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n) = perm :=
              (congrArg (fun p => insertAt (Fin.last n) (peeled.map Fin.castSucc) p)
                hpos_eq).symm.trans hinsert
            have hperm :=
              congrArg
                (fun v : Vector (Fin (n + 1)) (n + 1) =>
                  v[(⟨i.val + 1, hijSucc⟩ : Fin (n + 1))])
                hinsert_last
            exact hperm.symm.trans hraw
          have hget_i :
                perm[iUp] = (peeled[i]).castSucc := by
              have hraw :
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[iUp] =
                    (peeled[i]).castSucc := by
                have hraise : _root_.Hex.Matrix.raiseFinAbove (Fin.last n) i = iUp := by
                  apply Fin.ext
                  simp [_root_.Hex.Matrix.raiseFinAbove, iUp]
                have hbase := _root_.P2MLLL.t19afdfff.h76
                  (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n) i
                have hbase' :
                    (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[
                        _root_.Hex.Matrix.raiseFinAbove (Fin.last n) i] = (peeled[i]).castSucc := by
                  simpa using hbase
                exact (_root_.Hex.Matrix.vector_get_fin_congr
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))
                  hraise).symm.trans hbase'
              have hinsert_last :
                  insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n) = perm :=
                (congrArg (fun p => insertAt (Fin.last n) (peeled.map Fin.castSucc) p)
                  hpos_eq).symm.trans hinsert
              have hperm :=
                congrArg
                  (fun v : Vector (Fin (n + 1)) (n + 1) => v[iUp])
                  hinsert_last
              exact hperm.symm.trans hraw
          have hidx_up :
              (⟨iUp.val + 1, hijUp⟩ : Fin (n + 1)) =
                (⟨i.val + 1, hijSucc⟩ : Fin (n + 1)) := by
            apply Fin.ext
            simp [iUp]
          have hget_next_up :
              perm[(⟨iUp.val + 1, hijUp⟩ : Fin (n + 1))] =
                (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc :=
            (_root_.Hex.Matrix.vector_get_fin_congr perm hidx_up).trans hget_next
          rw [hget_next_up, hget_i]
          simpa [Fin.lt_def] using hdesc
      · have hk_lt_n : k < n := by
          have hk_le : k ≤ n := Nat.lt_succ_iff.mp hk
          have hpos_val : pos.val = k := rfl
          omega
        have hnextK : (⟨k, hk⟩ : Fin (n + 1)).val + 1 < n + 1 := by
          simpa using Nat.succ_lt_succ hk_lt_n
        refine ⟨(⟨k, hk⟩ : Fin (n + 1)), hnextK, ?_⟩
        · have hget_left : perm[(⟨k, hk⟩ : Fin (n + 1))] = Fin.last n := by
            have hraw :
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)[pos] = Fin.last n :=
              insertAt_get_self (Fin.last n) (peeled.map Fin.castSucc) pos
            have hperm :=
              congrArg (fun v : Vector (Fin (n + 1)) (n + 1) => v[pos]) hinsert
            exact hperm.symm.trans hraw
          have hget_right :
              perm[(⟨k + 1, hnextK⟩ : Fin (n + 1))] =
                (peeled[(⟨k, hk_lt_n⟩ : Fin n)]).castSucc := by
            have hraise :
                _root_.Hex.Matrix.raiseFinAbove pos (⟨k, hk_lt_n⟩ : Fin n) =
                  (⟨k + 1, hnextK⟩ : Fin (n + 1)) := by
              apply Fin.ext
              simp [_root_.Hex.Matrix.raiseFinAbove, pos]
            have hraw :
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)[
                    (⟨k + 1, hnextK⟩ : Fin (n + 1))] =
                  (peeled[(⟨k, hk_lt_n⟩ : Fin n)]).castSucc := by
              have hbase := _root_.P2MLLL.t19afdfff.h76
                (Fin.last n) (peeled.map Fin.castSucc) pos (⟨k, hk_lt_n⟩ : Fin n)
              have hbase' :
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)[
                      _root_.Hex.Matrix.raiseFinAbove pos (⟨k, hk_lt_n⟩ : Fin n)] =
                    (peeled[(⟨k, hk_lt_n⟩ : Fin n)]).castSucc := by
                simpa using hbase
              exact (_root_.Hex.Matrix.vector_get_fin_congr
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)
                hraise).symm.trans hbase'
            have hperm :=
              congrArg
                (fun v : Vector (Fin (n + 1)) (n + 1) =>
                  v[(⟨k + 1, hnextK⟩ : Fin (n + 1))])
                hinsert
            exact hperm.symm.trans hraw
          rw [hget_right, hget_left]
          simp [Fin.lt_def]
open _root_.P2MLLL.t19afdfff renaming h120 → Hex.Matrix.exists_adjacent_descent
open _root_.P2MLLL.t19afdfff renaming h120 → _p2mH120


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h134 {n : Nat}
    (perm : Vector (Fin n) n) (hmem : perm ∈ permutationVectors n)
    (hinv : inversionCount perm.toList = 0) :
    perm = Vector.ofFn fun i : Fin n => i := by
  induction n with
  | zero =>
      ext i hi
      omega
  | succ n ih =>
      have hnodup : perm.toList.Nodup := permutationVectors_nodup hmem
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          _root_.Hex.Matrix.finLast_idxOf_lt (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := _root_.Hex.Matrix.peelLastVector perm k hk hidx hnodup
      have hpeeled_nodup : peeled.toList.Nodup :=
        _root_.Hex.Matrix.peelLastVector_nodup perm k hk hidx hnodup
      have hpeeled_mem : peeled ∈ permutationVectors n :=
        permutationVectors_complete hpeeled_nodup
      let pos : Fin (n + 1) := ⟨k, hk⟩
      have hinsert :
          insertAt (Fin.last n) (peeled.map Fin.castSucc) pos = perm := by
        simpa [peeled, pos] using
          _root_.Hex.Matrix.insertAt_peelLastVector perm k hk hidx hnodup
      have hcount :
          inversionCount perm.toList =
            inversionCount peeled.toList + (n - pos.val) := by
        rw [← hinsert, insertAt_toList, vector_toList_map]
        simpa [peeled, pos, Vector.length_toList] using
          _root_.P2MLLL.t19afdfff.h110 peeled.toList pos.val (by
            simp [Vector.length_toList, pos]
            omega)
      have hpos : pos.val = n := by
        rw [hcount] at hinv
        omega
      have hpeeled_zero : inversionCount peeled.toList = 0 := by
        rw [hcount] at hinv
        omega
      have hpeeled_id : peeled = Vector.ofFn fun i : Fin n => i :=
        ih peeled hpeeled_mem hpeeled_zero
      rw [← hinsert, hpeeled_id]
      have hpos_eq : pos = Fin.last n := Fin.ext hpos
      rw [hpos_eq]
      have hvec :
          (Vector.ofFn fun i : Fin (n + 1) => i) =
            insertAt (Fin.last n)
              ((Vector.ofFn fun i : Fin n => i).map Fin.castSucc) (Fin.last n) := by
        ext r hr
        by_cases hlast : r = n
        · subst r
          simp [insertAt, List.getElem_insertIdx_self]
        · have hr_lt : r < n := by omega
          simp [insertAt, List.getElem_insertIdx_of_lt, hr_lt]
      exact hvec.symm
open _root_.P2MLLL.t19afdfff renaming h134 → Hex.Matrix.perm_eq_identity
open _root_.P2MLLL.t19afdfff renaming h134 → _p2mH134


set_option maxRecDepth 8192
/-- Multiplicativity of `detSign` under composition of permutation vectors.
The sign of a composed permutation equals the product of the component signs. -/
theorem _root_.P2MLLL.t19afdfff.h5
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (sigma tau : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n)
    (htau : tau ∈ permutationVectors n) :
    detSign (R := R) (composePermutationValues sigma tau) =
      detSign (R := R) sigma * detSign (R := R) tau := by
  suffices h : ∀ k, ∀ tau' : Vector (Fin n) n,
      tau' ∈ permutationVectors n →
      inversionCount tau'.toList = k →
      detSign (R := R) (composePermutationValues sigma tau') =
        detSign (R := R) sigma * detSign (R := R) tau' by
    exact h _ tau htau rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro tau' htau' hcount
    by_cases hk : k = 0
    · subst hk
      have hid : tau' = Vector.ofFn fun i : Fin n => i :=
        _root_.P2MLLL.t19afdfff.h134 tau' htau' hcount
      have hcompose_id :
          composePermutationValues sigma tau' = sigma := by
        rw [hid]
        ext r hr
        simp [composePermutationValues]
      rw [hcompose_id, hid, detSign_identity]
      grind
    · have hpos : 0 < inversionCount tau'.toList := by
        rw [hcount]; omega
      have hnodup_tau' := permutationVectors_nodup htau'
      obtain ⟨i, hij, hdesc⟩ := _root_.P2MLLL.t19afdfff.h120 tau' hnodup_tau' hpos
      let j : Fin n := ⟨i.val + 1, hij⟩
      have hij_eq : i.val + 1 = j.val := rfl
      have hi_ne_j : i ≠ j := by
        intro h
        have hvals := congrArg Fin.val h
        have hjval : j.val = i.val + 1 := rfl
        omega
      have hdesc' : tau'[j] < tau'[i] := hdesc
      have hcount_dec :
          inversionCount tau'.toList =
            inversionCount (_root_.Hex.Matrix.transposePermutationValues tau' i j).toList + 1 :=
        _root_.P2MLLL.t19afdfff.h133
          tau' hij_eq hdesc'
      have htau''_mem :
          _root_.Hex.Matrix.transposePermutationValues tau' i j ∈ permutationVectors n :=
        _root_.P2MLLL.t19afdfff.h139 i j htau'
      have hk_dec :
          inversionCount (_root_.Hex.Matrix.transposePermutationValues tau' i j).toList < k := by
        omega
      have ih_eq :=
        ih _ hk_dec (_root_.Hex.Matrix.transposePermutationValues tau' i j) htau''_mem rfl
      have hcompose :
          composePermutationValues sigma (_root_.Hex.Matrix.transposePermutationValues tau' i j) =
            _root_.Hex.Matrix.transposePermutationValues
              (composePermutationValues sigma tau') i j :=
        _root_.P2MLLL.t19afdfff.h118 sigma tau' i j
      have hsign_tau :
          detSign (R := R) tau' =
            -detSign (R := R) (_root_.Hex.Matrix.transposePermutationValues tau' i j) :=
        _root_.Hex.Matrix.detSign_transposeValues (R := R) tau' i j hnodup_tau' hi_ne_j
      have hnodup_compose :
          (composePermutationValues sigma tau').toList.Nodup :=
        _root_.P2MLLL.t19afdfff.h117
          (permutationVectors_nodup hsigma) hnodup_tau'
      have hsign_compose :
          detSign (R := R) (composePermutationValues sigma tau') =
            -detSign (R := R)
                (_root_.Hex.Matrix.transposePermutationValues
                  (composePermutationValues sigma tau') i j) :=
        _root_.Hex.Matrix.detSign_transposeValues (R := R)
          (composePermutationValues sigma tau') i j hnodup_compose hi_ne_j
      rw [hsign_compose, ← hcompose, ih_eq, hsign_tau]
      grind
open _root_.P2MLLL.t19afdfff renaming h5 → Hex.Matrix.detSign_composePermutationValues
open _root_.P2MLLL.t19afdfff renaming h5 → _p2mH5


set_option maxRecDepth 8192
/-- Inverse-orientation form of `detSign_composePermutationValues`: the sign of
`tau` is the sign of `sigma` times the sign of `composePermutationValues sigma tau`. -/
theorem _root_.P2MLLL.t19afdfff.h6
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (sigma tau : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n)
    (htau : tau ∈ permutationVectors n) :
    detSign (R := R) tau =
      detSign (R := R) sigma *
        detSign (R := R) (composePermutationValues sigma tau) := by
  have hmul :=
    _root_.P2MLLL.t19afdfff.h5 (R := R) sigma tau hsigma htau
  have hsq : detSign (R := R) sigma * detSign (R := R) sigma = 1 := by
    unfold detSign
    by_cases hp : inversionCount sigma.toList % 2 = 0
    · simp [hp]; grind
    · simp [hp]; grind
  rw [hmul]
  grind
open _root_.P2MLLL.t19afdfff renaming h6 → Hex.Matrix.detSign_eq_mul_detSign_composePermutationValues
open _root_.P2MLLL.t19afdfff renaming h6 → _p2mH6


end Matrix
open _root_.P2MLLL.t19afdfff renaming h5 → Hex.Matrix.detSign_composePermutationValues
open _root_.P2MLLL.t19afdfff renaming h5 → _p2mH5
open _root_.P2MLLL.t19afdfff renaming h6 → Hex.Matrix.detSign_eq_mul_detSign_composePermutationValues
open _root_.P2MLLL.t19afdfff renaming h6 → _p2mH6
open _root_.P2MLLL.t19afdfff renaming h112 → Hex.Matrix.composePermutationValues_get
open _root_.P2MLLL.t19afdfff renaming h112 → _p2mH112
open _root_.P2MLLL.t19afdfff renaming h113 → Hex.Matrix.composePermutationValues_left_inverse
open _root_.P2MLLL.t19afdfff renaming h113 → _p2mH113
open _root_.P2MLLL.t19afdfff renaming h114 → Hex.Matrix.composePermutationValues_left_involutive
open _root_.P2MLLL.t19afdfff renaming h114 → _p2mH114
open _root_.P2MLLL.t19afdfff renaming h115 → Hex.Matrix.composePermutationValues_left_map_permutationVectors_perm
open _root_.P2MLLL.t19afdfff renaming h115 → _p2mH115
open _root_.P2MLLL.t19afdfff renaming h116 → Hex.Matrix.composePermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h116 → _p2mH116
open _root_.P2MLLL.t19afdfff renaming h117 → Hex.Matrix.composePermutationValues_nodup
open _root_.P2MLLL.t19afdfff renaming h117 → _p2mH117
open _root_.P2MLLL.t19afdfff renaming h118 → Hex.Matrix.composePermutationValues_transposePermutationValues_right
open _root_.P2MLLL.t19afdfff renaming h118 → _p2mH118
open _root_.P2MLLL.t19afdfff renaming h119 → Hex.Matrix.detProduct_colPermute_vector
open _root_.P2MLLL.t19afdfff renaming h119 → _p2mH119
open _root_.P2MLLL.t19afdfff renaming h120 → Hex.Matrix.exists_adjacent_descent
open _root_.P2MLLL.t19afdfff renaming h120 → _p2mH120
open _root_.P2MLLL.t19afdfff renaming h121 → Hex.Matrix.finRange_map_finTranspose_perm
open _root_.P2MLLL.t19afdfff renaming h121 → _p2mH121
open _root_.P2MLLL.t19afdfff renaming h122 → Hex.Matrix.finTranspose_injective
open _root_.P2MLLL.t19afdfff renaming h122 → _p2mH122
open _root_.P2MLLL.t19afdfff renaming h123 → Hex.Matrix.finTranspose_involutive
open _root_.P2MLLL.t19afdfff renaming h123 → _p2mH123
open _root_.P2MLLL.t19afdfff renaming h124 → Hex.Matrix.inversePermutationValues_get_index
open _root_.P2MLLL.t19afdfff renaming h124 → _p2mH124
open _root_.P2MLLL.t19afdfff renaming h125 → Hex.Matrix.inversePermutationValues_get_value
open _root_.P2MLLL.t19afdfff renaming h125 → _p2mH125
open _root_.P2MLLL.t19afdfff renaming h126 → Hex.Matrix.inversePermutationValues_involutive
open _root_.P2MLLL.t19afdfff renaming h126 → _p2mH126
open _root_.P2MLLL.t19afdfff renaming h127 → Hex.Matrix.inversePermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h127 → _p2mH127
open _root_.P2MLLL.t19afdfff renaming h128 → Hex.Matrix.inversePermutationValues_nodup
open _root_.P2MLLL.t19afdfff renaming h128 → _p2mH128
open _root_.P2MLLL.t19afdfff renaming h129 → Hex.Matrix.inversePermutationVector_eq
open _root_.P2MLLL.t19afdfff renaming h129 → _p2mH129
open _root_.P2MLLL.t19afdfff renaming h130 → Hex.Matrix.inversePermutationVector_involutive_of_mem
open _root_.P2MLLL.t19afdfff renaming h130 → _p2mH130
open _root_.P2MLLL.t19afdfff renaming h131 → Hex.Matrix.inversePermutationVector_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h131 → _p2mH131
open _root_.P2MLLL.t19afdfff renaming h132 → Hex.Matrix.inversionCount_adjacent_swap_descent
open _root_.P2MLLL.t19afdfff renaming h132 → _p2mH132
open _root_.P2MLLL.t19afdfff renaming h133 → Hex.Matrix.inversionCount_transposePermutationValues_adjacent_descent
open _root_.P2MLLL.t19afdfff renaming h133 → _p2mH133
open _root_.P2MLLL.t19afdfff renaming h134 → Hex.Matrix.perm_eq_identity
open _root_.P2MLLL.t19afdfff renaming h134 → _p2mH134
open _root_.P2MLLL.t19afdfff renaming h135 → Hex.Matrix.permutationVectors_composePermutationValues_left_sum
open _root_.P2MLLL.t19afdfff renaming h135 → _p2mH135
open _root_.P2MLLL.t19afdfff renaming h136 → Hex.Matrix.swapPermutationValues_involutive
open _root_.P2MLLL.t19afdfff renaming h136 → _p2mH136
open _root_.P2MLLL.t19afdfff renaming h137 → Hex.Matrix.swapPermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h137 → _p2mH137
open _root_.P2MLLL.t19afdfff renaming h138 → Hex.Matrix.swapPermutationValues_toList_nodup
open _root_.P2MLLL.t19afdfff renaming h138 → _p2mH138
open _root_.P2MLLL.t19afdfff renaming h139 → Hex.Matrix.transposePermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h139 → _p2mH139
open _root_.P2MLLL.t19afdfff renaming h140 → Hex.Matrix.transposePermutationValues_toList_perm
open _root_.P2MLLL.t19afdfff renaming h140 → _p2mH140
open _root_.P2MLLL.t19afdfff renaming h141 → Hex.Matrix.vector_toList_eq
open _root_.P2MLLL.t19afdfff renaming h141 → _p2mH141

end Hex
open _root_.P2MLLL.t19afdfff renaming h5 → Hex.Matrix.detSign_composePermutationValues
open _root_.P2MLLL.t19afdfff renaming h5 → _p2mH5
open _root_.P2MLLL.t19afdfff renaming h6 → Hex.Matrix.detSign_eq_mul_detSign_composePermutationValues
open _root_.P2MLLL.t19afdfff renaming h6 → _p2mH6
open _root_.P2MLLL.t19afdfff renaming h112 → Hex.Matrix.composePermutationValues_get
open _root_.P2MLLL.t19afdfff renaming h112 → _p2mH112
open _root_.P2MLLL.t19afdfff renaming h113 → Hex.Matrix.composePermutationValues_left_inverse
open _root_.P2MLLL.t19afdfff renaming h113 → _p2mH113
open _root_.P2MLLL.t19afdfff renaming h114 → Hex.Matrix.composePermutationValues_left_involutive
open _root_.P2MLLL.t19afdfff renaming h114 → _p2mH114
open _root_.P2MLLL.t19afdfff renaming h115 → Hex.Matrix.composePermutationValues_left_map_permutationVectors_perm
open _root_.P2MLLL.t19afdfff renaming h115 → _p2mH115
open _root_.P2MLLL.t19afdfff renaming h116 → Hex.Matrix.composePermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h116 → _p2mH116
open _root_.P2MLLL.t19afdfff renaming h117 → Hex.Matrix.composePermutationValues_nodup
open _root_.P2MLLL.t19afdfff renaming h117 → _p2mH117
open _root_.P2MLLL.t19afdfff renaming h118 → Hex.Matrix.composePermutationValues_transposePermutationValues_right
open _root_.P2MLLL.t19afdfff renaming h118 → _p2mH118
open _root_.P2MLLL.t19afdfff renaming h119 → Hex.Matrix.detProduct_colPermute_vector
open _root_.P2MLLL.t19afdfff renaming h119 → _p2mH119
open _root_.P2MLLL.t19afdfff renaming h120 → Hex.Matrix.exists_adjacent_descent
open _root_.P2MLLL.t19afdfff renaming h120 → _p2mH120
open _root_.P2MLLL.t19afdfff renaming h121 → Hex.Matrix.finRange_map_finTranspose_perm
open _root_.P2MLLL.t19afdfff renaming h121 → _p2mH121
open _root_.P2MLLL.t19afdfff renaming h122 → Hex.Matrix.finTranspose_injective
open _root_.P2MLLL.t19afdfff renaming h122 → _p2mH122
open _root_.P2MLLL.t19afdfff renaming h123 → Hex.Matrix.finTranspose_involutive
open _root_.P2MLLL.t19afdfff renaming h123 → _p2mH123
open _root_.P2MLLL.t19afdfff renaming h124 → Hex.Matrix.inversePermutationValues_get_index
open _root_.P2MLLL.t19afdfff renaming h124 → _p2mH124
open _root_.P2MLLL.t19afdfff renaming h125 → Hex.Matrix.inversePermutationValues_get_value
open _root_.P2MLLL.t19afdfff renaming h125 → _p2mH125
open _root_.P2MLLL.t19afdfff renaming h126 → Hex.Matrix.inversePermutationValues_involutive
open _root_.P2MLLL.t19afdfff renaming h126 → _p2mH126
open _root_.P2MLLL.t19afdfff renaming h127 → Hex.Matrix.inversePermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h127 → _p2mH127
open _root_.P2MLLL.t19afdfff renaming h128 → Hex.Matrix.inversePermutationValues_nodup
open _root_.P2MLLL.t19afdfff renaming h128 → _p2mH128
open _root_.P2MLLL.t19afdfff renaming h129 → Hex.Matrix.inversePermutationVector_eq
open _root_.P2MLLL.t19afdfff renaming h129 → _p2mH129
open _root_.P2MLLL.t19afdfff renaming h130 → Hex.Matrix.inversePermutationVector_involutive_of_mem
open _root_.P2MLLL.t19afdfff renaming h130 → _p2mH130
open _root_.P2MLLL.t19afdfff renaming h131 → Hex.Matrix.inversePermutationVector_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h131 → _p2mH131
open _root_.P2MLLL.t19afdfff renaming h132 → Hex.Matrix.inversionCount_adjacent_swap_descent
open _root_.P2MLLL.t19afdfff renaming h132 → _p2mH132
open _root_.P2MLLL.t19afdfff renaming h133 → Hex.Matrix.inversionCount_transposePermutationValues_adjacent_descent
open _root_.P2MLLL.t19afdfff renaming h133 → _p2mH133
open _root_.P2MLLL.t19afdfff renaming h134 → Hex.Matrix.perm_eq_identity
open _root_.P2MLLL.t19afdfff renaming h134 → _p2mH134
open _root_.P2MLLL.t19afdfff renaming h135 → Hex.Matrix.permutationVectors_composePermutationValues_left_sum
open _root_.P2MLLL.t19afdfff renaming h135 → _p2mH135
open _root_.P2MLLL.t19afdfff renaming h136 → Hex.Matrix.swapPermutationValues_involutive
open _root_.P2MLLL.t19afdfff renaming h136 → _p2mH136
open _root_.P2MLLL.t19afdfff renaming h137 → Hex.Matrix.swapPermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h137 → _p2mH137
open _root_.P2MLLL.t19afdfff renaming h138 → Hex.Matrix.swapPermutationValues_toList_nodup
open _root_.P2MLLL.t19afdfff renaming h138 → _p2mH138
open _root_.P2MLLL.t19afdfff renaming h139 → Hex.Matrix.transposePermutationValues_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h139 → _p2mH139
open _root_.P2MLLL.t19afdfff renaming h140 → Hex.Matrix.transposePermutationValues_toList_perm
open _root_.P2MLLL.t19afdfff renaming h140 → _p2mH140
open _root_.P2MLLL.t19afdfff renaming h141 → Hex.Matrix.vector_toList_eq
open _root_.P2MLLL.t19afdfff renaming h141 → _p2mH141


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t19afdfff renaming h5 → Hex.Matrix.detSign_composePermutationValues
open _root_.P2MLLL.t19afdfff renaming h5 → _p2mH5
open _root_.P2MLLL.t19afdfff renaming h6 → Hex.Matrix.detSign_eq_mul_detSign_composePermutationValues
open _root_.P2MLLL.t19afdfff renaming h6 → _p2mH6

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section



set_option autoImplicit true



section

/-!
Determinant of elementary row and column operations.

Building on the permutation-vector structure in `HexDeterminant.Permutation`,
this module reindexes the Leibniz sum to read off the determinant's reaction to
the elementary operations: `det_identity`, `det_rowSwap`, `det_rowScale`,
`det_rowAdd`, `det_transpose`, `cofactor_transpose`, and the column analogues
`det_colPermute_vector`, `det_colSwap`, `det_colAdd`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}










set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h149 {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.idxOf i = perm.toList.idxOf j := by
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      _root_.Hex.Matrix.fin_idxOf_lt i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      _root_.Hex.Matrix.fin_idxOf_lt j (by simp [Vector.length_toList]) hnodup⟩
  have hpi_get : perm[pi] = i := by
    have hlt : perm.toList.idxOf i < perm.toList.length := by
      simpa [pi, Vector.length_toList] using pi.isLt
    exact List.getElem_idxOf (x := i) (xs := perm.toList) hlt
  have hswap :
      swapPermutationValues perm i j = _root_.Hex.Matrix.transposePermutationValues perm pi pj := by
    simpa [pi, pj] using _root_.Hex.Matrix.swapPermutationValues_eq perm i j hnodup
  have hpj_swap : (swapPermutationValues perm i j)[pj] = i := by
    rw [hswap, _root_.Hex.Matrix.transposePermutationValues_get]
    calc
      perm[finTranspose pi pj pj] = perm[pi] := by
        exact congrArg (fun x => perm[x]) (_root_.Hex.Matrix.finTranspose_right pi pj)
      _ = i := hpi_get
  have hnodupSwap := _root_.P2MLLL.t19afdfff.h138 perm i j hnodup
  have hpjLen : pj.val < (swapPermutationValues perm i j).toList.length := by
    simp [Vector.length_toList]
  have hidx :
      (swapPermutationValues perm i j).toList.idxOf
          ((swapPermutationValues perm i j).toList[pj.val]'hpjLen) = pj.val := by
    exact hnodupSwap.idxOf_getElem pj.val hpjLen
  have hget :
      (swapPermutationValues perm i j).toList[pj.val]'hpjLen = i := by
    exact hpj_swap
  rw [hget] at hidx
  exact hidx
open _root_.P2MLLL.t19afdfff renaming h149 → Hex.Matrix.swapPermutationValues_idxOf_left
open _root_.P2MLLL.t19afdfff renaming h149 → _p2mH149


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h150 {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.idxOf j = perm.toList.idxOf i := by
  have hcomm : swapPermutationValues perm i j = swapPermutationValues perm j i := by
    ext r hr
    apply Fin.val_eq_of_eq
    change (swapPermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
      (swapPermutationValues perm j i)[(⟨r, hr⟩ : Fin n)]
    repeat rw [_root_.Hex.Matrix.swapPermutationValues_get]
    by_cases hpi : perm[(⟨r, hr⟩ : Fin n)] = i
    · rw [hpi]
      exact (_root_.Hex.Matrix.finTranspose_left i j).trans (_root_.Hex.Matrix.finTranspose_right j i).symm
    · by_cases hpj : perm[(⟨r, hr⟩ : Fin n)] = j
      · rw [hpj]
        exact (_root_.Hex.Matrix.finTranspose_right i j).trans (_root_.Hex.Matrix.finTranspose_left j i).symm
      · exact
          (_root_.Hex.Matrix.finTranspose_of_ne i j perm[(⟨r, hr⟩ : Fin n)] hpi hpj).trans
            (_root_.Hex.Matrix.finTranspose_of_ne j i perm[(⟨r, hr⟩ : Fin n)] hpj hpi).symm
  rw [hcomm]
  exact _root_.P2MLLL.t19afdfff.h149 perm j i hnodup
open _root_.P2MLLL.t19afdfff renaming h150 → Hex.Matrix.swapPermutationValues_idxOf_right
open _root_.P2MLLL.t19afdfff renaming h150 → _p2mH150


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h148 {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    perm.toList.idxOf i ≠ perm.toList.idxOf j := by
  intro hidx
  have hiLt : perm.toList.idxOf i < perm.toList.length :=
    _root_.Hex.Matrix.fin_idxOf_lt i (by simp [Vector.length_toList]) hnodup
  have hjLt : perm.toList.idxOf j < perm.toList.length :=
    _root_.Hex.Matrix.fin_idxOf_lt j (by simp [Vector.length_toList]) hnodup
  have hiGet : perm.toList[perm.toList.idxOf i]'hiLt = i :=
    List.getElem_idxOf (x := i) (xs := perm.toList) hiLt
  have hjGet : perm.toList[perm.toList.idxOf j]'hjLt = j :=
    List.getElem_idxOf (x := j) (xs := perm.toList) hjLt
  apply h
  have hfin :
      (⟨perm.toList.idxOf i, hiLt⟩ : Fin perm.toList.length) =
        ⟨perm.toList.idxOf j, hjLt⟩ := Fin.ext hidx
  have hgeteq := congrArg (fun k : Fin perm.toList.length => perm.toList[k]) hfin
  exact hiGet.symm.trans (hgeteq.trans hjGet)
open _root_.P2MLLL.t19afdfff renaming h148 → Hex.Matrix.permutation_idxOf_ne
open _root_.P2MLLL.t19afdfff renaming h148 → _p2mH148


set_option maxRecDepth 8192
/-- When columns `src` and `dst` of `M` are equal, swapping those two values
in a permutation leaves the product term `detProduct M perm` unchanged. -/
 theorem _root_.P2MLLL.t19afdfff.h142 {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst])
    (perm : Vector (Fin n) n) :
    detProduct M perm = detProduct M (swapPermutationValues perm src dst) := by
  unfold detProduct
  simp only [Fin.foldl_eq_finRange_foldl, getElem_pair_eq_nested]
  apply _root_.P2MLLL.t19afdfff.h46
  intro r _hmem
  by_cases hsrc : perm[r] = src
  · have hswap : (swapPermutationValues perm src dst)[r] = dst := by
      rw [_root_.Hex.Matrix.swapPermutationValues_get]
      exact hsrc ▸ _root_.Hex.Matrix.finTranspose_left src dst
    calc
      M[r][perm[r]] = M[r][src] := congrArg (fun c => M[r][c]) hsrc
      _ = M[r][dst] := hcol r
      _ = M[r][(swapPermutationValues perm src dst)[r]] :=
          (congrArg (fun c => M[r][c]) hswap).symm
  · by_cases hdst : perm[r] = dst
    · have hswap : (swapPermutationValues perm src dst)[r] = src := by
        rw [_root_.Hex.Matrix.swapPermutationValues_get]
        exact hdst ▸ _root_.Hex.Matrix.finTranspose_right src dst
      calc
        M[r][perm[r]] = M[r][dst] := congrArg (fun c => M[r][c]) hdst
        _ = M[r][src] := (hcol r).symm
        _ = M[r][(swapPermutationValues perm src dst)[r]] :=
            (congrArg (fun c => M[r][c]) hswap).symm
    · have hswap : (swapPermutationValues perm src dst)[r] = perm[r] := by
        rw [_root_.Hex.Matrix.swapPermutationValues_get]
        exact _root_.Hex.Matrix.finTranspose_of_ne src dst perm[r] hsrc hdst
      exact (congrArg (fun c => M[r][c]) hswap).symm
open _root_.P2MLLL.t19afdfff renaming h142 → Hex.Matrix.detProduct_colDuplicate_swapValues
open _root_.P2MLLL.t19afdfff renaming h142 → _p2mH142


set_option maxRecDepth 8192
/-- For a nodup permutation with `src ≠ dst` and equal columns `src`, `dst`,
swapping those two values negates the signed determinant term `detTerm M perm`. -/
 theorem _root_.P2MLLL.t19afdfff.h143 {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst])
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm M perm = -detTerm M (swapPermutationValues perm src dst) := by
  unfold detTerm
  rw [_root_.P2MLLL.t19afdfff.h142 M src dst hcol perm,
    detSign_swapPermutationValues (R := R) perm src dst hnodup h]
  grind
open _root_.P2MLLL.t19afdfff renaming h143 → Hex.Matrix.detTerm_colDuplicate_swapValues
open _root_.P2MLLL.t19afdfff renaming h143 → _p2mH143
































set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h146 {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Bool) (f : β → R) :
    ∀ a b : R,
      xs.foldl (fun acc x => acc + f x) (a + b) =
        (xs.filter p).foldl (fun acc x => acc + f x) a +
          (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) b := by
  induction xs with
  | nil =>
      intro a b
      rfl
  | cons x xs ih =>
      intro a b
      simp only [List.foldl_cons]
      by_cases hp : p x
      · simp [hp]
        have hstart : a + b + f x = a + f x + b := by grind
        rw [hstart]
        exact ih (a + f x) b
      · simp [hp]
        have hstart : a + b + f x = a + (b + f x) := by grind
        rw [hstart]
        exact ih a (b + f x)
open _root_.P2MLLL.t19afdfff renaming h146 → Hex.Matrix.foldl_sum_filter_split_start
open _root_.P2MLLL.t19afdfff renaming h146 → _p2mH146


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h145 {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Bool) (f : β → R) :
    xs.foldl (fun acc x => acc + f x) 0 =
      (xs.filter p).foldl (fun acc x => acc + f x) 0 +
        (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) 0 := by
  calc
    xs.foldl (fun acc x => acc + f x) 0 =
      xs.foldl (fun acc x => acc + f x) ((0 : R) + 0) := by
        have hzero : (0 : R) + 0 = 0 := by grind
        rw [hzero]
    _ =
      (xs.filter p).foldl (fun acc x => acc + f x) 0 +
        (xs.filter fun x => !p x).foldl (fun acc x => acc + f x) 0 := by
      exact _root_.P2MLLL.t19afdfff.h146 xs p f 0 0
open _root_.P2MLLL.t19afdfff renaming h145 → Hex.Matrix.foldl_sum_filter_split
open _root_.P2MLLL.t19afdfff renaming h145 → _p2mH145


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h144 {R : Type u} [Zero R] [Add R]
    {β : Type v} {γ : Type w} (xs : List β) (map : β → γ) (f : γ → R) :
    (xs.map map).foldl (fun acc x => acc + f x) 0 =
      xs.foldl (fun acc x => acc + f (map x)) 0 := by
  simp [List.foldl_map]
open _root_.P2MLLL.t19afdfff renaming h144 → Hex.Matrix.foldl_det_sum_map
open _root_.P2MLLL.t19afdfff renaming h144 → _p2mH144










set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h147 {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst]) :
    (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 = 0 := by
  let p : Vector (Fin n) n → Bool :=
    fun perm => perm.toList.idxOf src < perm.toList.idxOf dst
  let term : Vector (Fin n) n → R := detTerm M
  have hsplit :=
    _root_.P2MLLL.t19afdfff.h145 (R := R) (permutationVectors n) p term
  rw [hsplit]
  have hright :
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 := by
    have hperm :
        (((permutationVectors n).filter p).map
            fun perm => swapPermutationValues perm src dst).Perm
          ((permutationVectors n).filter fun perm => !p perm) := by
      have hleftNodup :
          (((permutationVectors n).filter p).map
              fun perm => swapPermutationValues perm src dst).Nodup := by
        exact _root_.Hex.Matrix.list_nodup_map_of_injective
          (f := fun perm => swapPermutationValues perm src dst)
          (fun a b hab => by
            have h' := congrArg (fun perm => swapPermutationValues perm src dst) hab
            change
              swapPermutationValues (swapPermutationValues a src dst) src dst =
                swapPermutationValues (swapPermutationValues b src dst) src dst at h'
            rw [_root_.P2MLLL.t19afdfff.h136] at h'
            rw [_root_.P2MLLL.t19afdfff.h136] at h'
            exact h')
          (permutationVectors_nodup_list.filter p)
      have hrightNodup :
          ((permutationVectors n).filter fun perm => !p perm).Nodup :=
        permutationVectors_nodup_list.filter _
      apply (List.perm_ext_iff_of_nodup hleftNodup hrightNodup).mpr
      intro perm
      constructor
      · intro hmem
        simp only [List.mem_map, List.mem_filter] at hmem ⊢
        rcases hmem with ⟨pre, ⟨hpreMem, hpreP⟩, rfl⟩
        constructor
        · exact _root_.P2MLLL.t19afdfff.h137 src dst hpreMem
        · have hpreNodup := permutationVectors_nodup hpreMem
          simp [p] at hpreP ⊢
          rw [_root_.P2MLLL.t19afdfff.h149 pre src dst hpreNodup,
            _root_.P2MLLL.t19afdfff.h150 pre src dst hpreNodup]
          omega
      · intro hmem
        simp only [List.mem_filter] at hmem
        rcases hmem with ⟨hpermMem, hpfalse⟩
        simp only [List.mem_map, List.mem_filter]
        refine ⟨swapPermutationValues perm src dst,
          ⟨_root_.P2MLLL.t19afdfff.h137 src dst hpermMem, ?_⟩, ?_⟩
        · have hpermNodup := permutationVectors_nodup hpermMem
          simp [p] at hpfalse ⊢
          rw [_root_.P2MLLL.t19afdfff.h149 perm src dst hpermNodup,
            _root_.P2MLLL.t19afdfff.h150 perm src dst hpermNodup]
          have hneIdx := _root_.P2MLLL.t19afdfff.h148 perm src dst hpermNodup h
          omega
        · exact _root_.P2MLLL.t19afdfff.h136 perm src dst
    calc
      ((permutationVectors n).filter fun perm => !p perm).foldl
          (fun acc perm => acc + term perm) 0 =
        (((permutationVectors n).filter p).map
            fun perm => swapPermutationValues perm src dst).foldl
          (fun acc perm => acc + term perm) 0 := by
          exact (_root_.P2MLLL.t19afdfff.h44 term hperm 0).symm
      _ =
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 := by
          exact _root_.P2MLLL.t19afdfff.h144 ((permutationVectors n).filter p)
            (fun perm => swapPermutationValues perm src dst) term
  rw [hright]
  calc
    ((permutationVectors n).filter p).foldl (fun acc perm => acc + term perm) 0 +
        ((permutationVectors n).filter p).foldl
          (fun acc perm => acc + term (swapPermutationValues perm src dst)) 0 =
      ((permutationVectors n).filter p).foldl
          (fun acc perm =>
            acc + (term perm + term (swapPermutationValues perm src dst))) 0 := by
        exact (List.foldl_add_add
          ((permutationVectors n).filter p) term
          (fun perm => term (swapPermutationValues perm src dst))).symm
    _ = ((permutationVectors n).filter p).foldl (fun acc _ => acc + 0) 0 := by
        apply List.foldl_add_congr
        intro perm hmem
        simp only [term]
        rw [_root_.P2MLLL.t19afdfff.h143 M src dst h hcol perm]
        · grind
        · exact permutationVectors_nodup (List.mem_filter.mp hmem).1
    _ = 0 := by
        exact _root_.P2MLLL.t19afdfff.h45 ((permutationVectors n).filter p) 0
open _root_.P2MLLL.t19afdfff renaming h147 → Hex.Matrix.permutationVectors_duplicateCol_sum
open _root_.P2MLLL.t19afdfff renaming h147 → _p2mH147


































set_option maxRecDepth 8192
/-- Permuting columns multiplies the determinant by the sign of the column permutation. -/
theorem _root_.P2MLLL.t19afdfff.h7 {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (sigma : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n) :
    det ((ofFn fun r c => M[r][sigma[c]]) : Matrix R n n) =
      detSign (R := R) sigma * det M := by
  unfold det
  calc
    (permutationVectors n).foldl
        (fun acc tau =>
          acc + detTerm ((ofFn fun r c => M[r][sigma[c]]) : Matrix R n n) tau) 0 =
      (permutationVectors n).foldl
        (fun acc tau =>
          acc + detSign (R := R) sigma *
            detTerm M (composePermutationValues sigma tau)) 0 := by
        apply List.foldl_add_congr
        intro tau htau
        unfold detTerm
        rw [_root_.P2MLLL.t19afdfff.h119]
        rw [_root_.P2MLLL.t19afdfff.h6
          (R := R) sigma tau hsigma htau]
        grind
    _ =
      detSign (R := R) sigma *
        (permutationVectors n).foldl
          (fun acc tau => acc + detTerm M (composePermutationValues sigma tau)) 0 := by
        exact _root_.P2MLLL.t19afdfff.h41
          (permutationVectors n) (detSign (R := R) sigma)
          (fun tau => detTerm M (composePermutationValues sigma tau))
    _ =
      detSign (R := R) sigma *
        (permutationVectors n).foldl (fun acc tau => acc + detTerm M tau) 0 := by
        rw [_root_.P2MLLL.t19afdfff.h135
          (R := R) sigma hsigma (fun tau => detTerm M tau)]
open _root_.P2MLLL.t19afdfff renaming h7 → Hex.Matrix.det_colPermute_vector
open _root_.P2MLLL.t19afdfff renaming h7 → _p2mH7








end Matrix
open _root_.P2MLLL.t19afdfff renaming h7 → Hex.Matrix.det_colPermute_vector
open _root_.P2MLLL.t19afdfff renaming h7 → _p2mH7
open _root_.P2MLLL.t19afdfff renaming h142 → Hex.Matrix.detProduct_colDuplicate_swapValues
open _root_.P2MLLL.t19afdfff renaming h142 → _p2mH142
open _root_.P2MLLL.t19afdfff renaming h143 → Hex.Matrix.detTerm_colDuplicate_swapValues
open _root_.P2MLLL.t19afdfff renaming h143 → _p2mH143
open _root_.P2MLLL.t19afdfff renaming h144 → Hex.Matrix.foldl_det_sum_map
open _root_.P2MLLL.t19afdfff renaming h144 → _p2mH144
open _root_.P2MLLL.t19afdfff renaming h145 → Hex.Matrix.foldl_sum_filter_split
open _root_.P2MLLL.t19afdfff renaming h145 → _p2mH145
open _root_.P2MLLL.t19afdfff renaming h146 → Hex.Matrix.foldl_sum_filter_split_start
open _root_.P2MLLL.t19afdfff renaming h146 → _p2mH146
open _root_.P2MLLL.t19afdfff renaming h147 → Hex.Matrix.permutationVectors_duplicateCol_sum
open _root_.P2MLLL.t19afdfff renaming h147 → _p2mH147
open _root_.P2MLLL.t19afdfff renaming h148 → Hex.Matrix.permutation_idxOf_ne
open _root_.P2MLLL.t19afdfff renaming h148 → _p2mH148
open _root_.P2MLLL.t19afdfff renaming h149 → Hex.Matrix.swapPermutationValues_idxOf_left
open _root_.P2MLLL.t19afdfff renaming h149 → _p2mH149
open _root_.P2MLLL.t19afdfff renaming h150 → Hex.Matrix.swapPermutationValues_idxOf_right
open _root_.P2MLLL.t19afdfff renaming h150 → _p2mH150

end Hex
open _root_.P2MLLL.t19afdfff renaming h7 → Hex.Matrix.det_colPermute_vector
open _root_.P2MLLL.t19afdfff renaming h7 → _p2mH7
open _root_.P2MLLL.t19afdfff renaming h142 → Hex.Matrix.detProduct_colDuplicate_swapValues
open _root_.P2MLLL.t19afdfff renaming h142 → _p2mH142
open _root_.P2MLLL.t19afdfff renaming h143 → Hex.Matrix.detTerm_colDuplicate_swapValues
open _root_.P2MLLL.t19afdfff renaming h143 → _p2mH143
open _root_.P2MLLL.t19afdfff renaming h144 → Hex.Matrix.foldl_det_sum_map
open _root_.P2MLLL.t19afdfff renaming h144 → _p2mH144
open _root_.P2MLLL.t19afdfff renaming h145 → Hex.Matrix.foldl_sum_filter_split
open _root_.P2MLLL.t19afdfff renaming h145 → _p2mH145
open _root_.P2MLLL.t19afdfff renaming h146 → Hex.Matrix.foldl_sum_filter_split_start
open _root_.P2MLLL.t19afdfff renaming h146 → _p2mH146
open _root_.P2MLLL.t19afdfff renaming h147 → Hex.Matrix.permutationVectors_duplicateCol_sum
open _root_.P2MLLL.t19afdfff renaming h147 → _p2mH147
open _root_.P2MLLL.t19afdfff renaming h148 → Hex.Matrix.permutation_idxOf_ne
open _root_.P2MLLL.t19afdfff renaming h148 → _p2mH148
open _root_.P2MLLL.t19afdfff renaming h149 → Hex.Matrix.swapPermutationValues_idxOf_left
open _root_.P2MLLL.t19afdfff renaming h149 → _p2mH149
open _root_.P2MLLL.t19afdfff renaming h150 → Hex.Matrix.swapPermutationValues_idxOf_right
open _root_.P2MLLL.t19afdfff renaming h150 → _p2mH150


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t19afdfff renaming h7 → Hex.Matrix.det_colPermute_vector
open _root_.P2MLLL.t19afdfff renaming h7 → _p2mH7

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section



set_option autoImplicit true



section

/-!
Determinant column linearity for `hex-matrix`.

This module proves that `det` is multilinear in a single replaced column.
Working from the per-permutation product `detProduct` and signed term
`detTerm`, it establishes the additive `det_setCol_add`, the scalar
`det_setCol_smul`, and the finite-list/`Fin m` aggregated forms
`det_setCol_sum_list` and `det_setCol_sum_finRange`. It also collects the
duplicate-column/row vanishing lemmas (`det_eq_zero_of_col_eq`,
`det_eq_zero_of_row_eq`) and `det_setCol_add_otherCols` (column operations
preserve the determinant), plus the `columnSumMatrix` builder and the Fubini
sum-swap `List.foldl_add_comm` used by the Cauchy-Binet expansion.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

set_option maxRecDepth 8192
/-- The per-permutation product `detProduct` is additive in the replaced
column: splitting that column's entries as `v + w` splits the product as a sum. -/
 theorem _root_.P2MLLL.t19afdfff.h69 {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (setCol M dst (fun r => v r + w r)) perm =
      detProduct (setCol M dst v) perm +
        detProduct (setCol M dst w) perm := by
  let pivot : Fin n := ⟨perm.toList.idxOf dst,
    by
      simpa [Vector.length_toList] using
        _root_.Hex.Matrix.fin_idxOf_lt dst (by simp [Vector.length_toList]) hnodup⟩
  have hpivot : perm[pivot] = dst := by
    have hlt : perm.toList.idxOf dst < perm.toList.length :=
      _root_.Hex.Matrix.fin_idxOf_lt dst (by simp [Vector.length_toList]) hnodup
    have hget : perm.toList[perm.toList.idxOf dst]'hlt = dst :=
      List.getElem_idxOf (x := dst) (xs := perm.toList) hlt
    change perm.toList[pivot.val]'(by simp [Vector.length_toList, pivot.isLt]) = dst
    simp [pivot] at hget ⊢
  unfold detProduct
  simp only [Fin.foldl_eq_finRange_foldl, getElem_pair_eq_nested]
  calc
    (List.finRange n).foldl
        (fun acc i => acc * (setCol M dst (fun r => v r + w r))[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            (setCol M dst v)[x][perm[x]] + (setCol M dst w)[x][perm[x]]
          else
            (setCol M dst v)[x][perm[x]]) 1 := by
        apply _root_.P2MLLL.t19afdfff.h46
        intro x _hx
        rw [_root_.P2MLLL.t19afdfff.h22, _root_.P2MLLL.t19afdfff.h22, _root_.P2MLLL.t19afdfff.h22]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos hpivot, if_pos hpivot, if_pos rfl]
        · rw [if_neg hxp]
          have hperm_ne : perm[x] ≠ dst := by
            intro hperm
            have hxidx : perm.toList.idxOf perm[x] = x.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
            have hpidx : perm.toList.idxOf dst = pivot.val := rfl
            have hval : x.val = pivot.val := by
              rw [← hxidx, hperm, hpidx]
            exact hxp (Fin.ext hval)
          change (if perm[x] = dst then v x + w x else M[x][perm[x]]) =
            (if perm[x] = dst then v x else M[x][perm[x]])
          rw [if_neg hperm_ne, if_neg hperm_ne]
    _ =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            (setCol M dst v)[x][perm[x]] + (1 : R) * (setCol M dst w)[x][perm[x]]
          else
            (setCol M dst v)[x][perm[x]]) 1 := by
        apply _root_.P2MLLL.t19afdfff.h46
        intro x _hx
        by_cases hxp : x = pivot
        · rw [if_pos hxp]
          grind
        · simp [hxp]
    _ =
      (List.finRange n).foldl
          (fun acc x => acc * (setCol M dst v)[x][perm[x]]) 1 +
        (1 : R) * (List.finRange n).foldl
          (fun acc x => acc * (setCol M dst w)[x][perm[x]]) 1 := by
        exact
          _root_.P2MLLL.t19afdfff.h107 (R := R) (β := Fin n)
            (List.finRange n) pivot (1 : R)
            (fun x => (setCol M dst v)[x][perm[x]])
            (fun x => (setCol M dst w)[x][perm[x]])
            1 (List.mem_finRange pivot) (List.nodup_finRange n)
            (by
              intro x _hx hxp
              have hperm_ne : perm[x] ≠ dst := by
                intro hperm
                have hxidx : perm.toList.idxOf perm[x] = x.val := by
                  simpa [Vector.getElem_toList, Vector.length_toList] using
                    hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
                have hpidx : perm.toList.idxOf dst = pivot.val := rfl
                have hval : x.val = pivot.val := by
                  rw [← hxidx, hperm, hpidx]
                exact hxp (Fin.ext hval)
              change (setCol M dst w)[x][perm[x]] =
                (setCol M dst v)[x][perm[x]]
              rw [_root_.P2MLLL.t19afdfff.h22, _root_.P2MLLL.t19afdfff.h22]
              change (if perm[x] = dst then w x else M[x][perm[x]]) =
                (if perm[x] = dst then v x else M[x][perm[x]])
              rw [if_neg hperm_ne, if_neg hperm_ne])
    _ =
      (List.finRange n).foldl
          (fun acc x => acc * (setCol M dst v)[x][perm[x]]) 1 +
        (List.finRange n).foldl
          (fun acc x => acc * (setCol M dst w)[x][perm[x]]) 1 := by
        grind
open _root_.P2MLLL.t19afdfff renaming h69 → Hex.Matrix.detProduct_setCol_add
open _root_.P2MLLL.t19afdfff renaming h69 → _p2mH69


set_option maxRecDepth 8192
/-- The per-permutation product `detProduct` is homogeneous in the replaced
column: scaling that column's entries by `c` scales the product by `c`. -/
 theorem _root_.P2MLLL.t19afdfff.h70 {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct (setCol M dst (fun r => c * v r)) perm =
      c * detProduct (setCol M dst v) perm := by
  let pivot : Fin n := ⟨perm.toList.idxOf dst,
    by
      simpa [Vector.length_toList] using
        _root_.Hex.Matrix.fin_idxOf_lt dst (by simp [Vector.length_toList]) hnodup⟩
  have hpivot : perm[pivot] = dst := by
    have hlt : perm.toList.idxOf dst < perm.toList.length :=
      _root_.Hex.Matrix.fin_idxOf_lt dst (by simp [Vector.length_toList]) hnodup
    have hget : perm.toList[perm.toList.idxOf dst]'hlt = dst :=
      List.getElem_idxOf (x := dst) (xs := perm.toList) hlt
    change perm.toList[pivot.val]'(by simp [Vector.length_toList, pivot.isLt]) = dst
    simp [pivot] at hget ⊢
  unfold detProduct
  simp only [Fin.foldl_eq_finRange_foldl, getElem_pair_eq_nested]
  calc
    (List.finRange n).foldl
        (fun acc i => acc * (setCol M dst (fun r => c * v r))[i][perm[i]]) 1 =
      (List.finRange n).foldl
        (fun acc x =>
          acc * if x = pivot then
            c * (setCol M dst v)[x][perm[x]]
          else
            (setCol M dst v)[x][perm[x]]) 1 := by
        apply _root_.P2MLLL.t19afdfff.h46
        intro x _hx
        rw [_root_.P2MLLL.t19afdfff.h22, _root_.P2MLLL.t19afdfff.h22]
        by_cases hxp : x = pivot
        · subst x
          rw [if_pos hpivot, if_pos hpivot, if_pos rfl]
        · rw [if_neg hxp]
          have hperm_ne : perm[x] ≠ dst := by
            intro hperm
            have hxidx : perm.toList.idxOf perm[x] = x.val := by
              simpa [Vector.getElem_toList, Vector.length_toList] using
                hnodup.idxOf_getElem x.val (by simp [Vector.length_toList])
            have hpidx : perm.toList.idxOf dst = pivot.val := rfl
            have hval : x.val = pivot.val := by
              rw [← hxidx, hperm, hpidx]
            exact hxp (Fin.ext hval)
          change (if perm[x] = dst then c * v x else M[x][perm[x]]) =
            (if perm[x] = dst then v x else M[x][perm[x]])
          rw [if_neg hperm_ne, if_neg hperm_ne]
    _ =
      c * (List.finRange n).foldl
          (fun acc x => acc * (setCol M dst v)[x][perm[x]]) 1 := by
        exact
          _root_.P2MLLL.t19afdfff.h108 (R := R) (β := Fin n)
            (List.finRange n) pivot c
            (fun x => (setCol M dst v)[x][perm[x]])
            1 (List.mem_finRange pivot) (List.nodup_finRange n)
open _root_.P2MLLL.t19afdfff renaming h70 → Hex.Matrix.detProduct_setCol_smul
open _root_.P2MLLL.t19afdfff renaming h70 → _p2mH70


set_option maxRecDepth 8192
/-- The signed Leibniz term `detTerm` is additive in the replaced column:
splitting that column's entries as `v + w` splits the term as a sum. -/
 theorem _root_.P2MLLL.t19afdfff.h71 {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (setCol M dst (fun r => v r + w r)) perm =
      detTerm (setCol M dst v) perm + detTerm (setCol M dst w) perm := by
  unfold detTerm
  rw [_root_.P2MLLL.t19afdfff.h69 M dst v w perm hnodup]
  grind
open _root_.P2MLLL.t19afdfff renaming h71 → Hex.Matrix.detTerm_setCol_add
open _root_.P2MLLL.t19afdfff renaming h71 → _p2mH71


set_option maxRecDepth 8192
/-- The signed Leibniz term `detTerm` is homogeneous in the replaced column:
scaling that column's entries by `c` scales the term by `c`. -/
 theorem _root_.P2MLLL.t19afdfff.h72 {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (setCol M dst (fun r => c * v r)) perm =
      c * detTerm (setCol M dst v) perm := by
  unfold detTerm
  rw [_root_.P2MLLL.t19afdfff.h70 M dst c v perm hnodup]
  grind
open _root_.P2MLLL.t19afdfff renaming h72 → Hex.Matrix.detTerm_setCol_smul
open _root_.P2MLLL.t19afdfff renaming h72 → _p2mH72


set_option maxRecDepth 8192
/-- Determinant linearity in one replaced column, additive form. -/
theorem _root_.P2MLLL.t19afdfff.h15 {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R) :
    det (setCol M dst (fun r => v r + w r)) =
      det (setCol M dst v) + det (setCol M dst w) := by
  simp [det]
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (setCol M dst (fun r => v r + w r)) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm (setCol M dst v) perm +
            detTerm (setCol M dst w) perm)) 0 := by
        apply List.foldl_add_congr
        intro perm hmem
        exact _root_.P2MLLL.t19afdfff.h71 M dst v w perm (permutationVectors_nodup hmem)
    _ =
      (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (setCol M dst v) perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (setCol M dst w) perm) 0 := by
        exact List.foldl_add_add
          (permutationVectors n)
          (detTerm (setCol M dst v))
          (detTerm (setCol M dst w))
open _root_.P2MLLL.t19afdfff renaming h15 → Hex.Matrix.det_setCol_add
open _root_.P2MLLL.t19afdfff renaming h15 → _p2mH15


set_option maxRecDepth 8192
/-- Determinant linearity in one replaced column, scalar form. -/
theorem _root_.P2MLLL.t19afdfff.h16 {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) (c : R) (v : Fin n → R) :
    det (setCol M dst (fun r => c * v r)) =
      c * det (setCol M dst v) := by
  simp [det]
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (setCol M dst (fun r => c * v r)) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + c * detTerm (setCol M dst v) perm) 0 := by
        apply List.foldl_add_congr
        intro perm hmem
        exact _root_.P2MLLL.t19afdfff.h72 M dst c v perm (permutationVectors_nodup hmem)
    _ =
      c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (setCol M dst v) perm) 0 := by
        exact _root_.P2MLLL.t19afdfff.h41
          (permutationVectors n) c (detTerm (setCol M dst v))
open _root_.P2MLLL.t19afdfff renaming h16 → Hex.Matrix.det_setCol_smul
open _root_.P2MLLL.t19afdfff renaming h16 → _p2mH16




set_option maxRecDepth 8192
/-- The assembled determinant `det` vanishes when the replaced column is zero. -/
theorem _root_.P2MLLL.t19afdfff.h18 {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) :
    det (setCol M dst (fun _ => (0 : R))) = 0 := by
  have h := _root_.P2MLLL.t19afdfff.h16 M dst (0 : R) (fun _ => (1 : R))
  have hcol : (fun r : Fin n => (0 : R) * (1 : R)) = fun _ => (0 : R) := by
    funext r
    grind
  rw [hcol] at h
  grind
open _root_.P2MLLL.t19afdfff renaming h18 → Hex.Matrix.det_setCol_zero
open _root_.P2MLLL.t19afdfff renaming h18 → _p2mH18




set_option maxRecDepth 8192
/-- Determinant linearity in one replaced column, finite-list form. -/
theorem _root_.P2MLLL.t19afdfff.h17 {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (dst : Fin n) {β : Type v} (xs : List β)
    (coeff : β → R) (source : β → Fin n → R) :
    det (setCol M dst
        (fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0)) =
      xs.foldl
        (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 := by
  induction xs with
  | nil =>
      exact _root_.P2MLLL.t19afdfff.h18 M dst
  | cons x xs ih =>
      simp only [List.foldl_cons]
      let tail : Fin n → R :=
        fun r => xs.foldl (fun acc x => acc + coeff x * source x r) 0
      have hcol :
          (fun r : Fin n =>
              xs.foldl (fun acc x => acc + coeff x * source x r)
                (0 + coeff x * source x r)) =
            fun r => coeff x * source x r + tail r := by
        funext r
        rw [_root_.P2MLLL.t19afdfff.h39]
        simp [tail]
        grind
      calc
        det (setCol M dst
            (fun r => xs.foldl (fun acc x => acc + coeff x * source x r)
              (0 + coeff x * source x r))) =
          det (setCol M dst (fun r => coeff x * source x r + tail r)) := by
            rw [hcol]
        _ =
          det (setCol M dst (fun r => coeff x * source x r)) +
            det (setCol M dst tail) := by
            exact _root_.P2MLLL.t19afdfff.h15 M dst (fun r => coeff x * source x r) tail
        _ =
          coeff x * det (setCol M dst (source x)) +
            xs.foldl (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 := by
            rw [_root_.P2MLLL.t19afdfff.h16]
            simp [tail]
            rw [ih]
        _ =
          xs.foldl (fun acc x => acc + coeff x * det (setCol M dst (source x)))
            (0 + coeff x * det (setCol M dst (source x))) := by
            have hstart :=
              (_root_.P2MLLL.t19afdfff.h39 (R := R) xs
                (fun x => coeff x * det (setCol M dst (source x)))
                (0 + coeff x * det (setCol M dst (source x)))).symm
            calc
              coeff x * det (setCol M dst (source x)) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 =
                (0 + coeff x * det (setCol M dst (source x))) +
                  xs.foldl
                    (fun acc x => acc + coeff x * det (setCol M dst (source x))) 0 := by
                  grind
              _ =
                xs.foldl
                  (fun acc x => acc + coeff x * det (setCol M dst (source x)))
                  (0 + coeff x * det (setCol M dst (source x))) := hstart
open _root_.P2MLLL.t19afdfff renaming h17 → Hex.Matrix.det_setCol_sum_list
open _root_.P2MLLL.t19afdfff renaming h17 → _p2mH17






set_option maxRecDepth 8192
@[grind =]  theorem _root_.P2MLLL.t19afdfff.h75
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (r j : Fin n) :
    (columnSumMatrix source coeff)[r][j] =
      (List.finRange m).foldl (fun acc k => acc + coeff[(j, k)] * source[(r, k)]) 0 := by
  unfold columnSumMatrix
  rw [getElem_ofFn, Fin.foldl_eq_finRange_foldl]
open _root_.P2MLLL.t19afdfff renaming h75 → Hex.Matrix.getElem_columnSumMatrix
open _root_.P2MLLL.t19afdfff renaming h75 → _p2mH75












set_option maxRecDepth 8192
/-- A determinant with two equal columns is zero. -/
theorem _root_.P2MLLL.t19afdfff.h12 {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst)
    (hcol : ∀ r : Fin n, M[r][src] = M[r][dst]) :
    det M = 0 := by
  simpa [det] using _root_.P2MLLL.t19afdfff.h147 M src dst h hcol
open _root_.P2MLLL.t19afdfff renaming h12 → Hex.Matrix.det_eq_zero_of_col_eq
open _root_.P2MLLL.t19afdfff renaming h12 → _p2mH12






/-! # All-column ordered tuple expansion

Iterates `det_columnSumMatrix_expand_column` over every column to express
`det (columnSumMatrix source coeff)` as a sum over ordered column tuples.
Uses a list-based "left prefix" partial assignment, with a Fubini-style
sum-swap to align the iteration order with `columnTupleVectors`.
-/

set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h73 {R : Type u} [Lean.Grind.CommRing R]
    {β γ : Type v} (xs : List β) (ys : List γ) (f : β → γ → R) (z : R) :
    xs.foldl (fun acc x => ys.foldl (fun acc' y => acc' + f x y) acc) z =
      z + xs.foldl
        (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 := by
  induction xs generalizing z with
  | nil =>
      simp only [List.foldl_nil]
      grind
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [_root_.P2MLLL.t19afdfff.h39 ys (fun y => f x y) z,
        ih (z + ys.foldl (fun acc' y => acc' + f x y) 0)]
      rw [_root_.P2MLLL.t19afdfff.h39 xs
        (fun x => ys.foldl (fun acc' y => acc' + f x y) 0)
        (0 + ys.foldl (fun acc' y => acc' + f x y) 0)]
      grind
open _root_.P2MLLL.t19afdfff renaming h73 → Hex.Matrix.foldl_det_sum_nested_start
open _root_.P2MLLL.t19afdfff renaming h73 → _p2mH73


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h74 {R : Type u} [Lean.Grind.CommRing R]
    {β γ : Type v} (xs : List β) (ys : List γ) (f : β → γ → R) :
    xs.foldl (fun acc x => ys.foldl (fun acc' y => acc' + f x y) acc) 0 =
      xs.foldl
        (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 := by
  exact (_root_.P2MLLL.t19afdfff.h73 xs ys f (0 : R)).trans (by grind)
open _root_.P2MLLL.t19afdfff renaming h74 → Hex.Matrix.foldl_det_sum_nested_zero
open _root_.P2MLLL.t19afdfff renaming h74 → _p2mH74



end Matrix
open _root_.P2MLLL.t19afdfff renaming h12 → Hex.Matrix.det_eq_zero_of_col_eq
open _root_.P2MLLL.t19afdfff renaming h12 → _p2mH12
open _root_.P2MLLL.t19afdfff renaming h15 → Hex.Matrix.det_setCol_add
open _root_.P2MLLL.t19afdfff renaming h15 → _p2mH15
open _root_.P2MLLL.t19afdfff renaming h16 → Hex.Matrix.det_setCol_smul
open _root_.P2MLLL.t19afdfff renaming h16 → _p2mH16
open _root_.P2MLLL.t19afdfff renaming h17 → Hex.Matrix.det_setCol_sum_list
open _root_.P2MLLL.t19afdfff renaming h17 → _p2mH17
open _root_.P2MLLL.t19afdfff renaming h18 → Hex.Matrix.det_setCol_zero
open _root_.P2MLLL.t19afdfff renaming h18 → _p2mH18
open _root_.P2MLLL.t19afdfff renaming h69 → Hex.Matrix.detProduct_setCol_add
open _root_.P2MLLL.t19afdfff renaming h69 → _p2mH69
open _root_.P2MLLL.t19afdfff renaming h70 → Hex.Matrix.detProduct_setCol_smul
open _root_.P2MLLL.t19afdfff renaming h70 → _p2mH70
open _root_.P2MLLL.t19afdfff renaming h71 → Hex.Matrix.detTerm_setCol_add
open _root_.P2MLLL.t19afdfff renaming h71 → _p2mH71
open _root_.P2MLLL.t19afdfff renaming h72 → Hex.Matrix.detTerm_setCol_smul
open _root_.P2MLLL.t19afdfff renaming h72 → _p2mH72
open _root_.P2MLLL.t19afdfff renaming h73 → Hex.Matrix.foldl_det_sum_nested_start
open _root_.P2MLLL.t19afdfff renaming h73 → _p2mH73
open _root_.P2MLLL.t19afdfff renaming h74 → Hex.Matrix.foldl_det_sum_nested_zero
open _root_.P2MLLL.t19afdfff renaming h74 → _p2mH74
open _root_.P2MLLL.t19afdfff renaming h75 → Hex.Matrix.getElem_columnSumMatrix
open _root_.P2MLLL.t19afdfff renaming h75 → _p2mH75

end Hex
open _root_.P2MLLL.t19afdfff renaming h12 → Hex.Matrix.det_eq_zero_of_col_eq
open _root_.P2MLLL.t19afdfff renaming h12 → _p2mH12
open _root_.P2MLLL.t19afdfff renaming h15 → Hex.Matrix.det_setCol_add
open _root_.P2MLLL.t19afdfff renaming h15 → _p2mH15
open _root_.P2MLLL.t19afdfff renaming h16 → Hex.Matrix.det_setCol_smul
open _root_.P2MLLL.t19afdfff renaming h16 → _p2mH16
open _root_.P2MLLL.t19afdfff renaming h17 → Hex.Matrix.det_setCol_sum_list
open _root_.P2MLLL.t19afdfff renaming h17 → _p2mH17
open _root_.P2MLLL.t19afdfff renaming h18 → Hex.Matrix.det_setCol_zero
open _root_.P2MLLL.t19afdfff renaming h18 → _p2mH18
open _root_.P2MLLL.t19afdfff renaming h69 → Hex.Matrix.detProduct_setCol_add
open _root_.P2MLLL.t19afdfff renaming h69 → _p2mH69
open _root_.P2MLLL.t19afdfff renaming h70 → Hex.Matrix.detProduct_setCol_smul
open _root_.P2MLLL.t19afdfff renaming h70 → _p2mH70
open _root_.P2MLLL.t19afdfff renaming h71 → Hex.Matrix.detTerm_setCol_add
open _root_.P2MLLL.t19afdfff renaming h71 → _p2mH71
open _root_.P2MLLL.t19afdfff renaming h72 → Hex.Matrix.detTerm_setCol_smul
open _root_.P2MLLL.t19afdfff renaming h72 → _p2mH72
open _root_.P2MLLL.t19afdfff renaming h73 → Hex.Matrix.foldl_det_sum_nested_start
open _root_.P2MLLL.t19afdfff renaming h73 → _p2mH73
open _root_.P2MLLL.t19afdfff renaming h74 → Hex.Matrix.foldl_det_sum_nested_zero
open _root_.P2MLLL.t19afdfff renaming h74 → _p2mH74
open _root_.P2MLLL.t19afdfff renaming h75 → Hex.Matrix.getElem_columnSumMatrix
open _root_.P2MLLL.t19afdfff renaming h75 → _p2mH75


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t19afdfff renaming h12 → Hex.Matrix.det_eq_zero_of_col_eq
open _root_.P2MLLL.t19afdfff renaming h12 → _p2mH12
open _root_.P2MLLL.t19afdfff renaming h15 → Hex.Matrix.det_setCol_add
open _root_.P2MLLL.t19afdfff renaming h15 → _p2mH15
open _root_.P2MLLL.t19afdfff renaming h16 → Hex.Matrix.det_setCol_smul
open _root_.P2MLLL.t19afdfff renaming h16 → _p2mH16
open _root_.P2MLLL.t19afdfff renaming h17 → Hex.Matrix.det_setCol_sum_list
open _root_.P2MLLL.t19afdfff renaming h17 → _p2mH17
open _root_.P2MLLL.t19afdfff renaming h18 → Hex.Matrix.det_setCol_zero
open _root_.P2MLLL.t19afdfff renaming h18 → _p2mH18

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section




set_option autoImplicit true



section

/-!
Ordered column-tuple expansion underlying Cauchy-Binet for `hex-matrix`.

This module expands the determinant of a column-sum matrix as a finite sum
over all ordered column tuples drawn from `Fin m`. It defines the
column-selected minor `columnTupleMatrix`, its product coefficient
`columnTupleCoeff`, the tuple enumerator `columnTupleVectors`, and proves the
summands of repeated columns vanish. The headline results are
`det_columnSumMatrix_eq_sum_columnTuples` (the Mathlib-free multilinearity
form) and `det_gramMatrix_eq_sum_columnTuples`, which specializes it to a row
Gram matrix. The bulk of the file is a suffix-based partial-assignment
recursion (`columnSumMatrixWithSuffix`) aligning the iteration with
`columnTupleVectors`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}



set_option maxRecDepth 8192
/-- Entry `(r, c)` of the column-selected minor is the source entry
`A[r][cols c]`. -/
@[grind =] theorem _root_.P2MLLL.t19afdfff.h19 {R : Type u} {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m) (r c : Fin n) :
    (columnTupleMatrix A cols)[r][c] = A[r][cols c] := by
  unfold columnTupleMatrix
  rw [getElem_ofFn, getElem_pair_eq_nested]
open _root_.P2MLLL.t19afdfff renaming h19 → Hex.Matrix.getElem_columnTupleMatrix
open _root_.P2MLLL.t19afdfff renaming h19 → _p2mH19




set_option maxRecDepth 8192
/-- Applying the column-selection function at `i` reads the `i`-th entry
`cols[i]` of the tuple vector. -/
@[simp, grind =] theorem _root_.P2MLLL.t19afdfff.h3 {n m : Nat}
    (cols : Vector (Fin m) n) (i : Fin n) :
    columnTupleVectorFn cols i = cols[i] := rfl
open _root_.P2MLLL.t19afdfff renaming h3 → Hex.Matrix.columnTupleVectorFn_apply
open _root_.P2MLLL.t19afdfff renaming h3 → _p2mH3


set_option maxRecDepth 8192
/-- Reindexing the selected columns by a permutation is entrywise the generic
column permutation of the selected minor.

Unattributed: the LHS `[r][c]` is not in simp-normal form (`Fin.getElem_fin`
rewrites the `Fin` indices to `↑r`/`↑c`), and `grind =` rejects the pattern
because the columns `s sigma` appear only under the `fun i => s[sigma[i]]`
binder, so the LHS cannot instantiate them. Invoked explicitly via `rw`. -/
theorem _root_.P2MLLL.t19afdfff.h20
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (s : Vector (Fin m) n) (sigma : Vector (Fin n) n)
    (r c : Fin n) :
    (columnTupleMatrix A (fun i => s[sigma[i]]))[r][c] =
      (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]] := by
  rw [_root_.P2MLLL.t19afdfff.h19, _root_.P2MLLL.t19afdfff.h19]
  exact (congrArg (fun col : Fin m => A[r][col])
    (_root_.P2MLLL.t19afdfff.h3 s (sigma[c]))).symm
open _root_.P2MLLL.t19afdfff renaming h20 → Hex.Matrix.getElem_columnTupleMatrix_compose_perm
open _root_.P2MLLL.t19afdfff renaming h20 → _p2mH20


set_option maxRecDepth 8192
/-- Reindexing the selected columns by a permutation is the generic column
permutation of the selected minor. -/
theorem _root_.P2MLLL.t19afdfff.h2
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (s : Vector (Fin m) n) (sigma : Vector (Fin n) n) :
    columnTupleMatrix A (fun i => s[sigma[i]]) =
      (ofFn fun r c => (columnTupleMatrix A (columnTupleVectorFn s))[r][sigma[c]]) := by
  apply ext_getElem
  intro r c
  rw [_root_.P2MLLL.t19afdfff.h20, getElem_ofFn]
open _root_.P2MLLL.t19afdfff renaming h2 → Hex.Matrix.columnTupleMatrix_compose_perm_eq_colPermute
open _root_.P2MLLL.t19afdfff renaming h2 → _p2mH2


set_option maxRecDepth 8192
/-- Specialization of the generic column-permutation determinant sign theorem
to selected-minor matrices. -/
theorem _root_.P2MLLL.t19afdfff.h9
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (s : Vector (Fin m) n) (sigma : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n) :
    det (columnTupleMatrix A (fun i => s[sigma[i]])) =
      detSign (R := R) sigma * det (columnTupleMatrix A (columnTupleVectorFn s)) := by
  rw [_root_.P2MLLL.t19afdfff.h2 A s sigma]
  exact _root_.P2MLLL.t19afdfff.h7 (columnTupleMatrix A (columnTupleVectorFn s)) sigma hsigma
open _root_.P2MLLL.t19afdfff renaming h9 → Hex.Matrix.det_columnTupleMatrix_compose_perm
open _root_.P2MLLL.t19afdfff renaming h9 → _p2mH9




set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h56
    {n m : Nat} (cols : Fin (n + 1) → Fin m) :
    Vector.ofFn cols =
      insertAt (cols (Fin.last n)) (Vector.ofFn fun i : Fin n => cols i.castSucc)
        (Fin.last n) := by
  ext i hi
  apply Fin.val_eq_of_eq
  change (Vector.ofFn cols)[(⟨i, hi⟩ : Fin (n + 1))] =
    (insertAt (cols (Fin.last n)) (Vector.ofFn fun i : Fin n => cols i.castSucc)
      (Fin.last n))[(⟨i, hi⟩ : Fin (n + 1))]
  by_cases hlast : i = n
  · subst i
    simp [insertAt, List.getElem_insertIdx_self]
    exact congrArg cols (Fin.ext rfl)
  · have hi_lt : i < n := by omega
    simp [insertAt, List.getElem_insertIdx_of_lt, hi_lt]
open _root_.P2MLLL.t19afdfff renaming h56 → Hex.Matrix.columnTupleVectors_ofFn_succ
open _root_.P2MLLL.t19afdfff renaming h56 → _p2mH56


set_option maxRecDepth 8192
/-- Every ordered column-selection function occurs in `columnTupleVectors`. -/
theorem _root_.P2MLLL.t19afdfff.h4 {n m : Nat} (cols : Fin n → Fin m) :
    Vector.ofFn cols ∈ columnTupleVectors n m := by
  induction n with
  | zero =>
      simp [columnTupleVectors]
  | succ n ih =>
      rw [_root_.P2MLLL.t19afdfff.h56 cols, columnTupleVectors, List.mem_flatMap]
      refine ⟨Vector.ofFn fun i : Fin n => cols i.castSucc, ih (fun i => cols i.castSucc), ?_⟩
      rw [List.mem_map]
      exact ⟨cols (Fin.last n), List.mem_finRange (cols (Fin.last n)), rfl⟩
open _root_.P2MLLL.t19afdfff renaming h4 → Hex.Matrix.columnTupleVectors_mem_ofFn
open _root_.P2MLLL.t19afdfff renaming h4 → _p2mH4




set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h53 {n m : Nat} :
    ∀ (prefs : List (Vector (Fin m) n)), prefs.Nodup →
      (prefs.flatMap fun pref =>
        (List.finRange m).map fun c => insertAt c pref (Fin.last n)).Nodup
  | [], _ => by simp
  | pref :: prefs, hnodup => by
      simp only [List.flatMap_cons]
      simp only [List.nodup_cons] at hnodup
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · apply _root_.Hex.Matrix.list_nodup_map_on (List.nodup_finRange m)
        intro c _hc c' _hc' h
        exact (_root_.Hex.Matrix.insertAt_last_injective_pair h).1
      · exact P2MLLL.t19afdfff.h53 prefs hnodup.2
      · intro a hahead b hbsuffix hab
        rcases List.mem_map.mp hahead with ⟨c, _hc, rfl⟩
        rcases List.mem_flatMap.mp hbsuffix with ⟨pref', hpref', hb⟩
        rcases List.mem_map.mp hb with ⟨c', _hc', hb_eq⟩
        have hrec :
            insertAt c pref (Fin.last n) =
              insertAt c' pref' (Fin.last n) := hab.trans hb_eq.symm
        have hpref_eq := (_root_.Hex.Matrix.insertAt_last_injective_pair hrec).2
        subst hpref_eq
        exact hnodup.1 hpref'
open _root_.P2MLLL.t19afdfff renaming h53 → Hex.Matrix.columnTupleVectors_flatMap_last_nodup
open _root_.P2MLLL.t19afdfff renaming h53 → _p2mH53


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h55 {n m : Nat} :
    (columnTupleVectors n m).Nodup := by
  induction n with
  | zero =>
      simp [columnTupleVectors]
  | succ n ih =>
      rw [columnTupleVectors]
      exact _root_.P2MLLL.t19afdfff.h53 (columnTupleVectors n m) ih
open _root_.P2MLLL.t19afdfff renaming h55 → Hex.Matrix.columnTupleVectors_nodup
open _root_.P2MLLL.t19afdfff renaming h55 → _p2mH55






set_option maxRecDepth 8192
/-- An ordered column-tuple minor with a repeated selected column has determinant zero. -/
theorem _root_.P2MLLL.t19afdfff.h10
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m)
    {src dst : Fin n} (h : src ≠ dst) (hcols : cols src = cols dst) :
    det (columnTupleMatrix A cols) = 0 := by
  apply _root_.P2MLLL.t19afdfff.h12 (columnTupleMatrix A cols) src dst h
  intro r
  rw [_root_.P2MLLL.t19afdfff.h19, _root_.P2MLLL.t19afdfff.h19]
  exact congrArg (fun c : Fin m => A[r][c]) hcols
open _root_.P2MLLL.t19afdfff renaming h10 → Hex.Matrix.det_columnTupleMatrix_eq_zero_of_col_eq
open _root_.P2MLLL.t19afdfff renaming h10 → _p2mH10


set_option maxRecDepth 8192
/-- An ordered column-tuple minor with a non-injective selected-column map has
determinant zero. -/
theorem _root_.P2MLLL.t19afdfff.h11
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m)
    (hcols : ¬ Function.Injective cols) :
    det (columnTupleMatrix A cols) = 0 := by
  classical
  have hdup : ∃ src dst : Fin n, cols src = cols dst ∧ src ≠ dst := by
    rw [Function.Injective] at hcols
    rcases Classical.not_forall.mp hcols with ⟨src, hsrc⟩
    rcases Classical.not_forall.mp hsrc with ⟨dst, hdst⟩
    exact ⟨src, dst, (not_imp.mp hdst).1, fun h => (not_imp.mp hdst).2 h⟩
  rcases hdup with ⟨src, dst, hsame, hne⟩
  exact _root_.P2MLLL.t19afdfff.h10 A cols hne hsame
open _root_.P2MLLL.t19afdfff renaming h11 → Hex.Matrix.det_columnTupleMatrix_eq_zero_of_not_injective
open _root_.P2MLLL.t19afdfff renaming h11 → _p2mH11






/-! # Suffix-based partial assignment

We use a SUFFIX-based parametrization (chosen represents right-fixed columns)
to align with the natural recursion of `columnTupleVectors`, which factors out
the LAST element of the suffix. After Fubini sum-swap, the inductive step
reduces to identity matching of the per-term values. -/



set_option maxRecDepth 8192
@[grind =]  theorem _root_.P2MLLL.t19afdfff.h62
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) (r j : Fin n) :
    (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen)[r][j] =
      if h : n - chosen.length ≤ j.val then
        source[r][chosen[j.val - (n - chosen.length)]'(by
          have : j.val < n := j.isLt; omega)]
      else
        (List.finRange m).foldl
          (fun acc k => acc + coeff[j][k] * source[r][k]) 0 := by
  unfold _root_.Hex.Matrix.columnSumMatrixWithSuffix
  rw [getElem_ofFn]
  simp only [getElem_pair_eq_nested, Fin.foldl_eq_finRange_foldl]
open _root_.P2MLLL.t19afdfff renaming h62 → Hex.Matrix.getElem_columnSumMatrixWithSuffix
open _root_.P2MLLL.t19afdfff renaming h62 → _p2mH62


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h52
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) :
    _root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff [] = columnSumMatrix source coeff := by
  ext r hr c hc
  simp only [getElem_rows]
  change (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff [])[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnSumMatrix source coeff)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [_root_.P2MLLL.t19afdfff.h62, _root_.P2MLLL.t19afdfff.h75,
    dif_neg (show ¬ n - ([] : List (Fin m)).length ≤ c by simp; omega)]
  simp [getElem_pair_eq_nested]
open _root_.P2MLLL.t19afdfff renaming h52 → Hex.Matrix.columnSumMatrixWithSuffix_nil
open _root_.P2MLLL.t19afdfff renaming h52 → _p2mH52


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h51
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hfull : chosen.length = n) :
    _root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen =
      columnTupleMatrix source (fun j => chosen[j.val]'(by omega)) := by
  ext r hr c hc
  simp only [getElem_rows]
  change (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnTupleMatrix source (fun j => chosen[j.val]'(by omega)))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [_root_.P2MLLL.t19afdfff.h62, dif_pos (by omega : n - chosen.length ≤ c),
    _root_.P2MLLL.t19afdfff.h19]
  simp [hfull]
open _root_.P2MLLL.t19afdfff renaming h51 → Hex.Matrix.columnSumMatrixWithSuffix_eq
open _root_.P2MLLL.t19afdfff renaming h51 → _p2mH51


set_option maxRecDepth 8192
/-- Replacing the rightmost sum column of the suffix-partial matrix with a fixed
`source` column extends the suffix by prepending that selection. -/
 theorem _root_.P2MLLL.t19afdfff.h68
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) (c : Fin m) :
    setCol (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen)
        (⟨n - chosen.length - 1, by omega⟩ : Fin n) (fun r => source[r][c]) =
      _root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff (c :: chosen) := by
  ext r hr k hk2
  simp only [getElem_rows]
  change (setCol (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen)
      (⟨n - chosen.length - 1, by omega⟩ : Fin n) (fun r => source[r][c]))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)] =
    (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff (c :: chosen))[
      (⟨r, hr⟩ : Fin n)][(⟨k, hk2⟩ : Fin n)]
  rw [_root_.P2MLLL.t19afdfff.h22]
  simp only [_root_.P2MLLL.t19afdfff.h62]
  have hccons_len : (c :: chosen).length = chosen.length + 1 := rfl
  by_cases hkd : (⟨k, hk2⟩ : Fin n) = (⟨n - chosen.length - 1, by omega⟩ : Fin n)
  · have hkeq : k = n - chosen.length - 1 := by
      have := congrArg Fin.val hkd; simpa using this
    rw [if_pos hkd, dif_pos (show n - (c :: chosen).length ≤ k by rw [hccons_len]; omega)]
    have hsub0 : k - (n - (c :: chosen).length) = 0 := by rw [hccons_len]; omega
    have hgetval : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
        have : k < n := hk2; rw [hccons_len]; omega) = c := by
      have h1 : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
          have : k < n := hk2; rw [hccons_len]; omega) =
        (c :: chosen)[(0 : Nat)]'(by simp) := by
        congr 1
      rw [h1]
      rfl
    exact congrArg (fun x : Fin m => source[(⟨r, hr⟩ : Fin n)][x]) hgetval.symm
  · rw [if_neg hkd]
    have hkne : k ≠ n - chosen.length - 1 := fun h => hkd (Fin.ext h)
    by_cases hkge : n - chosen.length ≤ k
    · rw [dif_pos hkge]
      have hkge' : n - (c :: chosen).length ≤ k := by rw [hccons_len]; omega
      rw [dif_pos hkge']
      have hidx_eq : k - (n - (c :: chosen).length) = (k - (n - chosen.length)) + 1 := by
        rw [hccons_len]; omega
      have hgetval : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
          have : k < n := hk2; rw [hccons_len]; omega) =
        chosen[k - (n - chosen.length)]'(by have : k < n := hk2; omega) := by
        have h1 : (c :: chosen)[k - (n - (c :: chosen).length)]'(by
            have : k < n := hk2; rw [hccons_len]; omega) =
          (c :: chosen)[(k - (n - chosen.length)) + 1]'(by
            have : k < n := hk2; rw [hccons_len]; omega) := by
          congr 1
        rw [h1]
        rfl
      exact congrArg (fun x : Fin m => source[(⟨r, hr⟩ : Fin n)][x]) hgetval.symm
    · rw [dif_neg hkge]
      have hkge' : ¬ n - (c :: chosen).length ≤ k := by rw [hccons_len]; omega
      rw [dif_neg hkge']
open _root_.P2MLLL.t19afdfff renaming h68 → Hex.Matrix.setCol_columnSumMatrixWithSuffix_extend
open _root_.P2MLLL.t19afdfff renaming h68 → _p2mH68


set_option maxRecDepth 8192
/-- One-step expansion of the suffix-partial matrix: peel off the rightmost sum
column as a sum over `Fin m`. -/
 theorem _root_.P2MLLL.t19afdfff.h60
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    det (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen) =
      (List.finRange m).foldl
        (fun acc c => acc + coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          det (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff (c :: chosen))) 0 := by
  let dst : Fin n := ⟨n - chosen.length - 1, by omega⟩
  have hself :
      setCol (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen) dst
          (fun r => (List.finRange m).foldl
            (fun acc k => acc + coeff[dst][k] * source[r][k]) 0) =
        _root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen := by
    ext r hr c hc
    simp only [getElem_rows]
    change (setCol (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen) dst _)[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen)[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
    rw [_root_.P2MLLL.t19afdfff.h22, _root_.P2MLLL.t19afdfff.h62]
    by_cases hcd : (⟨c, hc⟩ : Fin n) = dst
    · rw [if_pos hcd, hcd]
      rw [dif_neg (show ¬ n - chosen.length ≤ dst.val by simp [dst]; omega)]
    · rw [if_neg hcd]
  have hsum := _root_.P2MLLL.t19afdfff.h17
      (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen) dst
      (List.finRange m) (fun k => coeff[dst][k]) (fun k r => source[r][k])
  rw [hself] at hsum
  rw [hsum]
  apply List.foldl_add_congr
  intro c _hc
  congr 2
  exact _root_.P2MLLL.t19afdfff.h68 source coeff chosen hk c
open _root_.P2MLLL.t19afdfff renaming h60 → Hex.Matrix.det_columnSumMatrixWithSuffix_expand
open _root_.P2MLLL.t19afdfff renaming h60 → _p2mH60




set_option maxRecDepth 8192
@[grind =]  theorem _root_.P2MLLL.t19afdfff.h49
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n)
    (i : Fin (n - chosen.length)) :
    (_root_.Hex.Matrix.assembleColumnsSuffix chosen pref hk)[
        (⟨i.val, by
          have hi : i.val < n - chosen.length := i.isLt
          omega⟩ : Fin n)] = pref[i] := by
  simp [_root_.Hex.Matrix.assembleColumnsSuffix]
open _root_.P2MLLL.t19afdfff renaming h49 → Hex.Matrix.assembleColumnsSuffix_left
open _root_.P2MLLL.t19afdfff renaming h49 → _p2mH49


set_option maxRecDepth 8192
@[grind =]  theorem _root_.P2MLLL.t19afdfff.h50
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n)
    (i : Fin chosen.length) :
    (_root_.Hex.Matrix.assembleColumnsSuffix chosen pref hk)[
        (⟨n - chosen.length + i.val, by
          have hi : i.val < chosen.length := i.isLt
          omega⟩ : Fin n)] = chosen[i] := by
  unfold _root_.Hex.Matrix.assembleColumnsSuffix
  simp [List.getElem_append_right]
open _root_.P2MLLL.t19afdfff renaming h50 → Hex.Matrix.assembleColumnsSuffix_right
open _root_.P2MLLL.t19afdfff renaming h50 → _p2mH50




set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h54
    {α : Type u} {m k l : Nat} (h : k = l)
    (f : α → Vector (Fin m) l → α) (init : α) :
    (columnTupleVectors l m).foldl f init =
      (columnTupleVectors k m).foldl
        (fun acc pref => f acc (_root_.Hex.Matrix.vectorLengthCast h pref)) init := by
  subst h
  rfl
open _root_.P2MLLL.t19afdfff renaming h54 → Hex.Matrix.columnTupleVectors_foldl_vectorLengthCast
open _root_.P2MLLL.t19afdfff renaming h54 → _p2mH54


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h48
    {n m : Nat} (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    _root_.Hex.Matrix.assembleColumnsSuffix chosen
        (_root_.Hex.Matrix.vectorLengthCast hlen
          (insertAt c pref (Fin.last (n - (c :: chosen).length))))
        (by
          have hcons : (c :: chosen).length = chosen.length + 1 := rfl
          omega) =
      _root_.Hex.Matrix.assembleColumnsSuffix (c :: chosen) pref hk := by
  apply Vector.toArray_inj.mp
  unfold _root_.Hex.Matrix.assembleColumnsSuffix
  simp only [_root_.Hex.Matrix.vectorLengthCast, Vector.toList, insertAt]
  have hidx : (Fin.last (n - (c :: chosen).length)).val = pref.toArray.toList.length := by
    simp
  rw [hidx, list_insertIdx_length]
  simp [List.append_assoc]
open _root_.P2MLLL.t19afdfff renaming h48 → Hex.Matrix.assembleColumnsSuffix_insertAt_last
open _root_.P2MLLL.t19afdfff renaming h48 → _p2mH48


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h61
    {R : Type u} [Lean.Grind.Ring R] {n m : Nat} (source : Matrix R n m)
    (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    det (columnTupleMatrix source
        (columnTupleVectorFn
          (_root_.Hex.Matrix.assembleColumnsSuffix chosen
            (_root_.Hex.Matrix.vectorLengthCast hlen
              (insertAt c pref (Fin.last (n - (c :: chosen).length))))
            (by
              have hcons : (c :: chosen).length = chosen.length + 1 := rfl
              omega)))) =
      det (columnTupleMatrix source
        (columnTupleVectorFn (_root_.Hex.Matrix.assembleColumnsSuffix (c :: chosen) pref hk))) := by
  rw [_root_.P2MLLL.t19afdfff.h48 chosen c pref hk hlen]
open _root_.P2MLLL.t19afdfff renaming h61 → Hex.Matrix.det_columnTupleMatrix_assembleColumnsSuffix_insertAt_last
open _root_.P2MLLL.t19afdfff renaming h61 → _p2mH61




set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h66
    {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (cols : Vector (Fin m) n) :
    _root_.Hex.Matrix.partialColumnTupleCoeff coeff [] cols = columnTupleCoeff coeff cols := by
  unfold _root_.Hex.Matrix.partialColumnTupleCoeff columnTupleCoeff
  simp only [Fin.foldl_eq_finRange_foldl]
  apply _root_.P2MLLL.t19afdfff.h46
  intro i _hmem
  congr 2
open _root_.P2MLLL.t19afdfff renaming h66 → Hex.Matrix.partialColumnTupleCoeff_nil
open _root_.P2MLLL.t19afdfff renaming h66 → _p2mH66


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h65
    {R : Type u} [Mul R] [OfNat R 1] {n m rem : Nat}
    (coeff : Matrix R n m) (c : Fin m) (pref : Vector (Fin m) rem)
    (hrem : rem < n) :
    Fin.foldl (rem + 1)
        (fun acc i => acc * coeff[(⟨i.val, by
          have hi : i.val < rem + 1 := i.isLt
          omega⟩ : Fin n)][(insertAt c pref (Fin.last rem))[i]]) 1 =
      Fin.foldl rem
          (fun acc i => acc * coeff[(⟨i.val, by
            have hi : i.val < rem := i.isLt
            omega⟩ : Fin n)][pref[i]]) 1 *
        coeff[(⟨rem, hrem⟩ : Fin n)][c] := by
  simp only [Fin.foldl_eq_finRange_foldl]
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr 1
  · simp only [List.foldl_map]
    apply _root_.P2MLLL.t19afdfff.h46
    intro i _hmem
    change
      coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][(insertAt c pref (Fin.last rem))[i.castSucc]] =
      coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][pref[i]]
    exact congrArg
      (fun x : Fin m => coeff[(⟨i.val, by
        have hi : i.val < rem := i.isLt
        omega⟩ : Fin n)][x])
      (insertAt_last_get_castSucc c pref i)
  · change
      coeff[(⟨rem, hrem⟩ : Fin n)][(insertAt c pref (Fin.last rem))[Fin.last rem]] =
        coeff[(⟨rem, hrem⟩ : Fin n)][c]
    exact congrArg (fun x : Fin m => coeff[(⟨rem, hrem⟩ : Fin n)][x])
      (insertAt_get_self c pref (Fin.last rem))
open _root_.P2MLLL.t19afdfff renaming h65 → Hex.Matrix.partialColumnTupleCoeff_insertAt_last_fold
open _root_.P2MLLL.t19afdfff renaming h65 → _p2mH65


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h67
    {R : Type u} [Mul R] [OfNat R 1] {n m k : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : k = n - chosen.length) (hkn : k ≤ n) (v : Vector (Fin m) k) :
    _root_.Hex.Matrix.partialColumnTupleCoeff coeff chosen (_root_.Hex.Matrix.vectorLengthCast hk v) =
    Fin.foldl k
      (fun acc (i : Fin k) => acc *
        coeff[(⟨i.val, Nat.lt_of_lt_of_le i.isLt hkn⟩ : Fin n)][v[i]]) 1 := by
  subst hk
  unfold _root_.Hex.Matrix.partialColumnTupleCoeff
  rcases v with ⟨xs, hx⟩
  simp only [getElem_pair_eq_nested]
  rfl
open _root_.P2MLLL.t19afdfff renaming h67 → Hex.Matrix.partialColumnTupleCoeff_vectorLengthCast
open _root_.P2MLLL.t19afdfff renaming h67 → _p2mH67


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h64
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m)) (c : Fin m)
    (pref : Vector (Fin m) (n - (c :: chosen).length))
    (hk : (c :: chosen).length ≤ n)
    (hlen : (n - (c :: chosen).length) + 1 = n - chosen.length := by
      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
      omega) :
    _root_.Hex.Matrix.partialColumnTupleCoeff coeff chosen
        (_root_.Hex.Matrix.vectorLengthCast hlen
          (insertAt c pref (Fin.last (n - (c :: chosen).length)))) =
      coeff[(⟨n - chosen.length - 1, by
        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
        omega⟩ : Fin n)][c] *
        _root_.Hex.Matrix.partialColumnTupleCoeff coeff (c :: chosen) pref := by
  have hcons : (c :: chosen).length = chosen.length + 1 := rfl
  have hrem_lt : n - (c :: chosen).length < n := by omega
  have hlen_le : (n - (c :: chosen).length) + 1 ≤ n := by omega
  rw [_root_.P2MLLL.t19afdfff.h67 coeff chosen hlen hlen_le
      (insertAt c pref (Fin.last (n - (c :: chosen).length)))]
  rw [_root_.P2MLLL.t19afdfff.h65 coeff c pref hrem_lt]
  unfold _root_.Hex.Matrix.partialColumnTupleCoeff
  simp only [getElem_pair_eq_nested]
  refine Eq.trans (Lean.Grind.CommSemiring.mul_comm _ _) ?_
  congr 1
open _root_.P2MLLL.t19afdfff renaming h64 → Hex.Matrix.partialColumnTupleCoeff_insertAt_last
open _root_.P2MLLL.t19afdfff renaming h64 → _p2mH64


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h57
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    (columnTupleVectors ((n - (chosen.length + 1)) + 1) m).foldl
        (fun acc pref => acc +
          _root_.Hex.Matrix.partialColumnTupleCoeff coeff chosen
            (_root_.Hex.Matrix.vectorLengthCast (by omega : (n - (chosen.length + 1)) + 1 =
              n - chosen.length) pref) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (_root_.Hex.Matrix.assembleColumnsSuffix chosen
                  (_root_.Hex.Matrix.vectorLengthCast (by omega : (n - (chosen.length + 1)) + 1 =
                    n - chosen.length) pref) (by omega))))) 0 =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                _root_.Hex.Matrix.partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (_root_.Hex.Matrix.assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0 := by
  have hlen :
      n - chosen.length = (n - (chosen.length + 1)) + 1 := by
    omega
  change
    (((columnTupleVectors (n - (chosen.length + 1)) m).flatMap fun pref =>
        (List.finRange m).map fun c =>
          insertAt c pref (Fin.last (n - (chosen.length + 1)))).foldl
        (fun acc pref => acc +
          _root_.Hex.Matrix.partialColumnTupleCoeff coeff chosen (_root_.Hex.Matrix.vectorLengthCast hlen.symm pref) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (_root_.Hex.Matrix.assembleColumnsSuffix chosen (_root_.Hex.Matrix.vectorLengthCast hlen.symm pref) (by omega))))) 0) =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                _root_.Hex.Matrix.partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (_root_.Hex.Matrix.assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0
  rw [_root_.P2MLLL.t19afdfff.h40]
  simp only [List.foldl_map]
  rw [_root_.P2MLLL.t19afdfff.h74, _root_.P2MLLL.t19afdfff.h38]
  apply List.foldl_add_congr
  intro c _hc
  have hfactor :
      (columnTupleVectors (n - (chosen.length + 1)) m).foldl
          (fun acc pref => acc +
            coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
              (_root_.Hex.Matrix.partialColumnTupleCoeff coeff (c :: chosen) pref *
                det (columnTupleMatrix source
                  (columnTupleVectorFn
                    (_root_.Hex.Matrix.assembleColumnsSuffix (c :: chosen) pref (by
                      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                      omega)))))) 0 =
        coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          (columnTupleVectors (n - (chosen.length + 1)) m).foldl
            (fun acc pref => acc +
              _root_.Hex.Matrix.partialColumnTupleCoeff coeff (c :: chosen) pref *
                det (columnTupleMatrix source
                  (columnTupleVectorFn
                    (_root_.Hex.Matrix.assembleColumnsSuffix (c :: chosen) pref (by
                      have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                      omega))))) 0 := by
    exact _root_.P2MLLL.t19afdfff.h41
      (columnTupleVectors (n - (chosen.length + 1)) m)
      (coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c])
      (fun pref =>
        _root_.Hex.Matrix.partialColumnTupleCoeff coeff (c :: chosen) pref *
          det (columnTupleMatrix source
            (columnTupleVectorFn
              (_root_.Hex.Matrix.assembleColumnsSuffix (c :: chosen) pref (by
                have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                omega)))))
  change
    (columnTupleVectors (n - (chosen.length + 1)) m).foldl
        (fun acc' x => acc' +
          _root_.Hex.Matrix.partialColumnTupleCoeff coeff chosen
              (_root_.Hex.Matrix.vectorLengthCast hlen.symm (insertAt c x (Fin.last (n - (chosen.length + 1))))) *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (_root_.Hex.Matrix.assembleColumnsSuffix chosen
                  (_root_.Hex.Matrix.vectorLengthCast hlen.symm (insertAt c x (Fin.last (n - (chosen.length + 1)))))
                  (by omega))))) 0 =
      coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
        (columnTupleVectors (n - (chosen.length + 1)) m).foldl
          (fun acc pref => acc +
            _root_.Hex.Matrix.partialColumnTupleCoeff coeff (c :: chosen) pref *
              det (columnTupleMatrix source
                (columnTupleVectorFn
                  (_root_.Hex.Matrix.assembleColumnsSuffix (c :: chosen) pref (by
                    have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                    omega))))) 0
  rw [← hfactor]
  apply List.foldl_add_congr
  intro pref _hpref
  have hcast :
      (n - (chosen.length + 1)) + 1 = n - chosen.length := by
    omega
  have hkcons : (c :: chosen).length ≤ n := by
    have hcons : (c :: chosen).length = chosen.length + 1 := rfl
    omega
  have hcoeff :
      _root_.Hex.Matrix.partialColumnTupleCoeff coeff chosen
          (_root_.Hex.Matrix.vectorLengthCast hcast
            (insertAt c pref (Fin.last (n - (chosen.length + 1))))) =
        coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
          _root_.Hex.Matrix.partialColumnTupleCoeff coeff (c :: chosen) pref := by
    simpa only [List.length_cons] using
      (_root_.P2MLLL.t19afdfff.h64 coeff chosen c pref hkcons hcast)
  have hdet :
      det (columnTupleMatrix source
          (columnTupleVectorFn
            (_root_.Hex.Matrix.assembleColumnsSuffix chosen
              (_root_.Hex.Matrix.vectorLengthCast hcast
                (insertAt c pref (Fin.last (n - (chosen.length + 1)))))
              (by omega)))) =
        det (columnTupleMatrix source
          (columnTupleVectorFn (_root_.Hex.Matrix.assembleColumnsSuffix (c :: chosen) pref hkcons))) := by
    simpa only [List.length_cons] using
      (_root_.P2MLLL.t19afdfff.h61
        source chosen c pref hkcons hcast)
  rw [hcoeff, hdet]
  grind
open _root_.P2MLLL.t19afdfff renaming h57 → Hex.Matrix.columnTupleVectors_suffix_rhs_step
open _root_.P2MLLL.t19afdfff renaming h57 → _p2mH57


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h58
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length < n) :
    (columnTupleVectors (n - chosen.length) m).foldl
        (fun acc pref => acc +
          _root_.Hex.Matrix.partialColumnTupleCoeff coeff chosen pref *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (_root_.Hex.Matrix.assembleColumnsSuffix chosen pref (by omega))))) 0 =
      (List.finRange m).foldl
        (fun acc c => acc +
          coeff[(⟨n - chosen.length - 1, by omega⟩ : Fin n)][c] *
            (columnTupleVectors (n - (c :: chosen).length) m).foldl
              (fun acc pref => acc +
                _root_.Hex.Matrix.partialColumnTupleCoeff coeff (c :: chosen) pref *
                  det (columnTupleMatrix source
                    (columnTupleVectorFn
                      (_root_.Hex.Matrix.assembleColumnsSuffix (c :: chosen) pref (by
                        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
                        omega))))) 0) 0 := by
  rw [_root_.P2MLLL.t19afdfff.h54
    (by omega : (n - (chosen.length + 1)) + 1 = n - chosen.length)]
  exact _root_.P2MLLL.t19afdfff.h57 source coeff chosen hk
open _root_.P2MLLL.t19afdfff renaming h58 → Hex.Matrix.columnTupleVectors_suffix_rhs_step_natural
open _root_.P2MLLL.t19afdfff renaming h58 → _p2mH58


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h47
    {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length))
    (hk : chosen.length ≤ n) (hfull : chosen.length = n) :
    _root_.Hex.Matrix.assembleColumnsSuffix chosen pref hk =
      Vector.ofFn (fun j : Fin n => chosen[j.val]'(by omega)) := by
  ext i hi
  apply Fin.val_eq_of_eq
  change (_root_.Hex.Matrix.assembleColumnsSuffix chosen pref hk)[(⟨i, hi⟩ : Fin n)] =
    (Vector.ofFn (fun j : Fin n => chosen[j.val]'(by omega)))[(⟨i, hi⟩ : Fin n)]
  simpa [hfull] using
    (_root_.P2MLLL.t19afdfff.h50 chosen pref hk (⟨i, by omega⟩ : Fin chosen.length))
open _root_.P2MLLL.t19afdfff renaming h47 → Hex.Matrix.assembleColumnsSuffix_full
open _root_.P2MLLL.t19afdfff renaming h47 → _p2mH47


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h63
    {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length))
    (hfull : chosen.length = n) :
    _root_.Hex.Matrix.partialColumnTupleCoeff coeff chosen pref = 1 := by
  subst n
  unfold _root_.Hex.Matrix.partialColumnTupleCoeff
  rw [Fin.foldl_eq_finRange_foldl]
  have hlist : List.finRange (chosen.length - chosen.length) = [] := by
    rw [Nat.sub_self]; rfl
  rw [hlist]
  rfl
open _root_.P2MLLL.t19afdfff renaming h63 → Hex.Matrix.partialColumnTupleCoeff_full
open _root_.P2MLLL.t19afdfff renaming h63 → _p2mH63


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h59
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m))
    (hk : chosen.length ≤ n) :
    det (_root_.Hex.Matrix.columnSumMatrixWithSuffix source coeff chosen) =
      (columnTupleVectors (n - chosen.length) m).foldl
        (fun acc pref => acc +
          _root_.Hex.Matrix.partialColumnTupleCoeff coeff chosen pref *
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (_root_.Hex.Matrix.assembleColumnsSuffix chosen pref hk)))) 0 := by
  by_cases hfull : chosen.length = n
  ·
      have hfull : chosen.length = n := by omega
      subst n
      rw [_root_.P2MLLL.t19afdfff.h51 source coeff chosen hfull]
      let hcast : 0 = chosen.length - chosen.length := by omega
      rw [_root_.P2MLLL.t19afdfff.h54 hcast]
      simp only [columnTupleVectors, List.foldl_cons, List.foldl_nil]
      rw [_root_.P2MLLL.t19afdfff.h63 coeff chosen (_root_.Hex.Matrix.vectorLengthCast hcast #v[]) hfull]
      have hdet :
          det (columnTupleMatrix source (fun j : Fin chosen.length => chosen[j.val]'(by omega))) =
            det (columnTupleMatrix source
              (columnTupleVectorFn
                (_root_.Hex.Matrix.assembleColumnsSuffix chosen (_root_.Hex.Matrix.vectorLengthCast hcast #v[]) hk))) := by
        apply congrArg det
        apply congrArg (columnTupleMatrix source)
        funext j
        simp [columnTupleVectorFn]
        rw [_root_.P2MLLL.t19afdfff.h47 chosen (_root_.Hex.Matrix.vectorLengthCast hcast #v[]) hk hfull]
        simp
      rw [hdet]
      grind
  ·
      have hklt : chosen.length < n := by omega
      rw [_root_.P2MLLL.t19afdfff.h60 source coeff chosen hklt,
        _root_.P2MLLL.t19afdfff.h58 source coeff chosen hklt]
      apply List.foldl_add_congr
      intro c _hc
      congr 2
      have hkcons : (c :: chosen).length ≤ n := by
        have hcons : (c :: chosen).length = chosen.length + 1 := rfl
        omega
      exact P2MLLL.t19afdfff.h59 source coeff (c :: chosen) hkcons
termination_by n - chosen.length
decreasing_by
  simp_wf
  omega
open _root_.P2MLLL.t19afdfff renaming h59 → Hex.Matrix.det_columnSumMatrixWithSuffix_eq_sum
open _root_.P2MLLL.t19afdfff renaming h59 → _p2mH59


set_option maxRecDepth 8192
/-- Expand the determinant of a matrix whose columns are linear combinations
of source columns as a finite sum over all ordered column tuples. This is the
Mathlib-free multilinearity form behind Cauchy-Binet. -/
theorem _root_.P2MLLL.t19afdfff.h8
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) :
    det (columnSumMatrix source coeff) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc +
          columnTupleCoeff coeff cols *
            det (columnTupleMatrix source (columnTupleVectorFn cols))) 0 := by
  rw [← _root_.P2MLLL.t19afdfff.h52 source coeff,
    _root_.P2MLLL.t19afdfff.h59 source coeff [] (by simp)]
  apply List.foldl_add_congr
  intro cols _hcols
  have hcoeff : _root_.Hex.Matrix.partialColumnTupleCoeff coeff [] cols = columnTupleCoeff coeff cols :=
    _root_.P2MLLL.t19afdfff.h66 coeff cols
  have hdet :
      det (columnTupleMatrix source (columnTupleVectorFn (_root_.Hex.Matrix.assembleColumnsSuffix [] cols (by simp)))) =
        det (columnTupleMatrix source (columnTupleVectorFn cols)) := by
    apply congrArg det
    apply ext_getElem
    intro i j
    rw [_root_.P2MLLL.t19afdfff.h19, _root_.P2MLLL.t19afdfff.h19]
    exact congrArg (fun x : Fin m => source[i][x])
      (_root_.P2MLLL.t19afdfff.h49 ([] : List (Fin m)) cols (by simp)
        (⟨j.val, by simp⟩))
  rw [hcoeff, hdet]
open _root_.P2MLLL.t19afdfff renaming h8 → Hex.Matrix.det_columnSumMatrix_eq_sum_columnTuples
open _root_.P2MLLL.t19afdfff renaming h8 → _p2mH8


set_option maxRecDepth 8192
/-- The determinant of a row Gram matrix expands as the ordered-column tuple
sum induced by the generic column-sum determinant expansion. -/
theorem _root_.P2MLLL.t19afdfff.h13
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    det (gramMatrix A) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc +
          columnTupleCoeff A cols *
            det (columnTupleMatrix A (columnTupleVectorFn cols))) 0 := by
  have hgram : gramMatrix A = columnSumMatrix A A := by
    apply ext_getElem
    intro r c
    rw [getElem_gramMatrix, _root_.P2MLLL.t19afdfff.h75]
    simp only [Vector.dotProduct, getElem_row, getElem_pair_eq_nested]
    apply List.foldl_add_congr
    intro k _hk
    exact Lean.Grind.CommSemiring.mul_comm A[r][k] A[c][k]
  rw [hgram]
  exact _root_.P2MLLL.t19afdfff.h8 A A
open _root_.P2MLLL.t19afdfff renaming h13 → Hex.Matrix.det_gramMatrix_eq_sum_columnTuples
open _root_.P2MLLL.t19afdfff renaming h13 → _p2mH13



end Matrix
open _root_.P2MLLL.t19afdfff renaming h2 → Hex.Matrix.columnTupleMatrix_compose_perm_eq_colPermute
open _root_.P2MLLL.t19afdfff renaming h2 → _p2mH2
open _root_.P2MLLL.t19afdfff renaming h3 → Hex.Matrix.columnTupleVectorFn_apply
open _root_.P2MLLL.t19afdfff renaming h3 → _p2mH3
open _root_.P2MLLL.t19afdfff renaming h4 → Hex.Matrix.columnTupleVectors_mem_ofFn
open _root_.P2MLLL.t19afdfff renaming h4 → _p2mH4
open _root_.P2MLLL.t19afdfff renaming h8 → Hex.Matrix.det_columnSumMatrix_eq_sum_columnTuples
open _root_.P2MLLL.t19afdfff renaming h8 → _p2mH8
open _root_.P2MLLL.t19afdfff renaming h9 → Hex.Matrix.det_columnTupleMatrix_compose_perm
open _root_.P2MLLL.t19afdfff renaming h9 → _p2mH9
open _root_.P2MLLL.t19afdfff renaming h10 → Hex.Matrix.det_columnTupleMatrix_eq_zero_of_col_eq
open _root_.P2MLLL.t19afdfff renaming h10 → _p2mH10
open _root_.P2MLLL.t19afdfff renaming h11 → Hex.Matrix.det_columnTupleMatrix_eq_zero_of_not_injective
open _root_.P2MLLL.t19afdfff renaming h11 → _p2mH11
open _root_.P2MLLL.t19afdfff renaming h13 → Hex.Matrix.det_gramMatrix_eq_sum_columnTuples
open _root_.P2MLLL.t19afdfff renaming h13 → _p2mH13
open _root_.P2MLLL.t19afdfff renaming h19 → Hex.Matrix.getElem_columnTupleMatrix
open _root_.P2MLLL.t19afdfff renaming h19 → _p2mH19
open _root_.P2MLLL.t19afdfff renaming h20 → Hex.Matrix.getElem_columnTupleMatrix_compose_perm
open _root_.P2MLLL.t19afdfff renaming h20 → _p2mH20
open _root_.P2MLLL.t19afdfff renaming h47 → Hex.Matrix.assembleColumnsSuffix_full
open _root_.P2MLLL.t19afdfff renaming h47 → _p2mH47
open _root_.P2MLLL.t19afdfff renaming h48 → Hex.Matrix.assembleColumnsSuffix_insertAt_last
open _root_.P2MLLL.t19afdfff renaming h48 → _p2mH48
open _root_.P2MLLL.t19afdfff renaming h49 → Hex.Matrix.assembleColumnsSuffix_left
open _root_.P2MLLL.t19afdfff renaming h49 → _p2mH49
open _root_.P2MLLL.t19afdfff renaming h50 → Hex.Matrix.assembleColumnsSuffix_right
open _root_.P2MLLL.t19afdfff renaming h50 → _p2mH50
open _root_.P2MLLL.t19afdfff renaming h51 → Hex.Matrix.columnSumMatrixWithSuffix_eq
open _root_.P2MLLL.t19afdfff renaming h51 → _p2mH51
open _root_.P2MLLL.t19afdfff renaming h52 → Hex.Matrix.columnSumMatrixWithSuffix_nil
open _root_.P2MLLL.t19afdfff renaming h52 → _p2mH52
open _root_.P2MLLL.t19afdfff renaming h53 → Hex.Matrix.columnTupleVectors_flatMap_last_nodup
open _root_.P2MLLL.t19afdfff renaming h53 → _p2mH53
open _root_.P2MLLL.t19afdfff renaming h54 → Hex.Matrix.columnTupleVectors_foldl_vectorLengthCast
open _root_.P2MLLL.t19afdfff renaming h54 → _p2mH54
open _root_.P2MLLL.t19afdfff renaming h55 → Hex.Matrix.columnTupleVectors_nodup
open _root_.P2MLLL.t19afdfff renaming h55 → _p2mH55
open _root_.P2MLLL.t19afdfff renaming h56 → Hex.Matrix.columnTupleVectors_ofFn_succ
open _root_.P2MLLL.t19afdfff renaming h56 → _p2mH56
open _root_.P2MLLL.t19afdfff renaming h57 → Hex.Matrix.columnTupleVectors_suffix_rhs_step
open _root_.P2MLLL.t19afdfff renaming h57 → _p2mH57
open _root_.P2MLLL.t19afdfff renaming h58 → Hex.Matrix.columnTupleVectors_suffix_rhs_step_natural
open _root_.P2MLLL.t19afdfff renaming h58 → _p2mH58
open _root_.P2MLLL.t19afdfff renaming h59 → Hex.Matrix.det_columnSumMatrixWithSuffix_eq_sum
open _root_.P2MLLL.t19afdfff renaming h59 → _p2mH59
open _root_.P2MLLL.t19afdfff renaming h60 → Hex.Matrix.det_columnSumMatrixWithSuffix_expand
open _root_.P2MLLL.t19afdfff renaming h60 → _p2mH60
open _root_.P2MLLL.t19afdfff renaming h61 → Hex.Matrix.det_columnTupleMatrix_assembleColumnsSuffix_insertAt_last
open _root_.P2MLLL.t19afdfff renaming h61 → _p2mH61
open _root_.P2MLLL.t19afdfff renaming h62 → Hex.Matrix.getElem_columnSumMatrixWithSuffix
open _root_.P2MLLL.t19afdfff renaming h62 → _p2mH62
open _root_.P2MLLL.t19afdfff renaming h63 → Hex.Matrix.partialColumnTupleCoeff_full
open _root_.P2MLLL.t19afdfff renaming h63 → _p2mH63
open _root_.P2MLLL.t19afdfff renaming h64 → Hex.Matrix.partialColumnTupleCoeff_insertAt_last
open _root_.P2MLLL.t19afdfff renaming h64 → _p2mH64
open _root_.P2MLLL.t19afdfff renaming h65 → Hex.Matrix.partialColumnTupleCoeff_insertAt_last_fold
open _root_.P2MLLL.t19afdfff renaming h65 → _p2mH65
open _root_.P2MLLL.t19afdfff renaming h66 → Hex.Matrix.partialColumnTupleCoeff_nil
open _root_.P2MLLL.t19afdfff renaming h66 → _p2mH66
open _root_.P2MLLL.t19afdfff renaming h67 → Hex.Matrix.partialColumnTupleCoeff_vectorLengthCast
open _root_.P2MLLL.t19afdfff renaming h67 → _p2mH67
open _root_.P2MLLL.t19afdfff renaming h68 → Hex.Matrix.setCol_columnSumMatrixWithSuffix_extend
open _root_.P2MLLL.t19afdfff renaming h68 → _p2mH68

end Hex
open _root_.P2MLLL.t19afdfff renaming h2 → Hex.Matrix.columnTupleMatrix_compose_perm_eq_colPermute
open _root_.P2MLLL.t19afdfff renaming h2 → _p2mH2
open _root_.P2MLLL.t19afdfff renaming h3 → Hex.Matrix.columnTupleVectorFn_apply
open _root_.P2MLLL.t19afdfff renaming h3 → _p2mH3
open _root_.P2MLLL.t19afdfff renaming h4 → Hex.Matrix.columnTupleVectors_mem_ofFn
open _root_.P2MLLL.t19afdfff renaming h4 → _p2mH4
open _root_.P2MLLL.t19afdfff renaming h8 → Hex.Matrix.det_columnSumMatrix_eq_sum_columnTuples
open _root_.P2MLLL.t19afdfff renaming h8 → _p2mH8
open _root_.P2MLLL.t19afdfff renaming h9 → Hex.Matrix.det_columnTupleMatrix_compose_perm
open _root_.P2MLLL.t19afdfff renaming h9 → _p2mH9
open _root_.P2MLLL.t19afdfff renaming h10 → Hex.Matrix.det_columnTupleMatrix_eq_zero_of_col_eq
open _root_.P2MLLL.t19afdfff renaming h10 → _p2mH10
open _root_.P2MLLL.t19afdfff renaming h11 → Hex.Matrix.det_columnTupleMatrix_eq_zero_of_not_injective
open _root_.P2MLLL.t19afdfff renaming h11 → _p2mH11
open _root_.P2MLLL.t19afdfff renaming h13 → Hex.Matrix.det_gramMatrix_eq_sum_columnTuples
open _root_.P2MLLL.t19afdfff renaming h13 → _p2mH13
open _root_.P2MLLL.t19afdfff renaming h19 → Hex.Matrix.getElem_columnTupleMatrix
open _root_.P2MLLL.t19afdfff renaming h19 → _p2mH19
open _root_.P2MLLL.t19afdfff renaming h20 → Hex.Matrix.getElem_columnTupleMatrix_compose_perm
open _root_.P2MLLL.t19afdfff renaming h20 → _p2mH20
open _root_.P2MLLL.t19afdfff renaming h47 → Hex.Matrix.assembleColumnsSuffix_full
open _root_.P2MLLL.t19afdfff renaming h47 → _p2mH47
open _root_.P2MLLL.t19afdfff renaming h48 → Hex.Matrix.assembleColumnsSuffix_insertAt_last
open _root_.P2MLLL.t19afdfff renaming h48 → _p2mH48
open _root_.P2MLLL.t19afdfff renaming h49 → Hex.Matrix.assembleColumnsSuffix_left
open _root_.P2MLLL.t19afdfff renaming h49 → _p2mH49
open _root_.P2MLLL.t19afdfff renaming h50 → Hex.Matrix.assembleColumnsSuffix_right
open _root_.P2MLLL.t19afdfff renaming h50 → _p2mH50
open _root_.P2MLLL.t19afdfff renaming h51 → Hex.Matrix.columnSumMatrixWithSuffix_eq
open _root_.P2MLLL.t19afdfff renaming h51 → _p2mH51
open _root_.P2MLLL.t19afdfff renaming h52 → Hex.Matrix.columnSumMatrixWithSuffix_nil
open _root_.P2MLLL.t19afdfff renaming h52 → _p2mH52
open _root_.P2MLLL.t19afdfff renaming h53 → Hex.Matrix.columnTupleVectors_flatMap_last_nodup
open _root_.P2MLLL.t19afdfff renaming h53 → _p2mH53
open _root_.P2MLLL.t19afdfff renaming h54 → Hex.Matrix.columnTupleVectors_foldl_vectorLengthCast
open _root_.P2MLLL.t19afdfff renaming h54 → _p2mH54
open _root_.P2MLLL.t19afdfff renaming h55 → Hex.Matrix.columnTupleVectors_nodup
open _root_.P2MLLL.t19afdfff renaming h55 → _p2mH55
open _root_.P2MLLL.t19afdfff renaming h56 → Hex.Matrix.columnTupleVectors_ofFn_succ
open _root_.P2MLLL.t19afdfff renaming h56 → _p2mH56
open _root_.P2MLLL.t19afdfff renaming h57 → Hex.Matrix.columnTupleVectors_suffix_rhs_step
open _root_.P2MLLL.t19afdfff renaming h57 → _p2mH57
open _root_.P2MLLL.t19afdfff renaming h58 → Hex.Matrix.columnTupleVectors_suffix_rhs_step_natural
open _root_.P2MLLL.t19afdfff renaming h58 → _p2mH58
open _root_.P2MLLL.t19afdfff renaming h59 → Hex.Matrix.det_columnSumMatrixWithSuffix_eq_sum
open _root_.P2MLLL.t19afdfff renaming h59 → _p2mH59
open _root_.P2MLLL.t19afdfff renaming h60 → Hex.Matrix.det_columnSumMatrixWithSuffix_expand
open _root_.P2MLLL.t19afdfff renaming h60 → _p2mH60
open _root_.P2MLLL.t19afdfff renaming h61 → Hex.Matrix.det_columnTupleMatrix_assembleColumnsSuffix_insertAt_last
open _root_.P2MLLL.t19afdfff renaming h61 → _p2mH61
open _root_.P2MLLL.t19afdfff renaming h62 → Hex.Matrix.getElem_columnSumMatrixWithSuffix
open _root_.P2MLLL.t19afdfff renaming h62 → _p2mH62
open _root_.P2MLLL.t19afdfff renaming h63 → Hex.Matrix.partialColumnTupleCoeff_full
open _root_.P2MLLL.t19afdfff renaming h63 → _p2mH63
open _root_.P2MLLL.t19afdfff renaming h64 → Hex.Matrix.partialColumnTupleCoeff_insertAt_last
open _root_.P2MLLL.t19afdfff renaming h64 → _p2mH64
open _root_.P2MLLL.t19afdfff renaming h65 → Hex.Matrix.partialColumnTupleCoeff_insertAt_last_fold
open _root_.P2MLLL.t19afdfff renaming h65 → _p2mH65
open _root_.P2MLLL.t19afdfff renaming h66 → Hex.Matrix.partialColumnTupleCoeff_nil
open _root_.P2MLLL.t19afdfff renaming h66 → _p2mH66
open _root_.P2MLLL.t19afdfff renaming h67 → Hex.Matrix.partialColumnTupleCoeff_vectorLengthCast
open _root_.P2MLLL.t19afdfff renaming h67 → _p2mH67
open _root_.P2MLLL.t19afdfff renaming h68 → Hex.Matrix.setCol_columnSumMatrixWithSuffix_extend
open _root_.P2MLLL.t19afdfff renaming h68 → _p2mH68


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t19afdfff renaming h2 → Hex.Matrix.columnTupleMatrix_compose_perm_eq_colPermute
open _root_.P2MLLL.t19afdfff renaming h2 → _p2mH2
open _root_.P2MLLL.t19afdfff renaming h3 → Hex.Matrix.columnTupleVectorFn_apply
open _root_.P2MLLL.t19afdfff renaming h3 → _p2mH3
open _root_.P2MLLL.t19afdfff renaming h4 → Hex.Matrix.columnTupleVectors_mem_ofFn
open _root_.P2MLLL.t19afdfff renaming h4 → _p2mH4
open _root_.P2MLLL.t19afdfff renaming h8 → Hex.Matrix.det_columnSumMatrix_eq_sum_columnTuples
open _root_.P2MLLL.t19afdfff renaming h8 → _p2mH8
open _root_.P2MLLL.t19afdfff renaming h9 → Hex.Matrix.det_columnTupleMatrix_compose_perm
open _root_.P2MLLL.t19afdfff renaming h9 → _p2mH9
open _root_.P2MLLL.t19afdfff renaming h10 → Hex.Matrix.det_columnTupleMatrix_eq_zero_of_col_eq
open _root_.P2MLLL.t19afdfff renaming h10 → _p2mH10
open _root_.P2MLLL.t19afdfff renaming h11 → Hex.Matrix.det_columnTupleMatrix_eq_zero_of_not_injective
open _root_.P2MLLL.t19afdfff renaming h11 → _p2mH11
open _root_.P2MLLL.t19afdfff renaming h13 → Hex.Matrix.det_gramMatrix_eq_sum_columnTuples
open _root_.P2MLLL.t19afdfff renaming h13 → _p2mH13
open _root_.P2MLLL.t19afdfff renaming h19 → Hex.Matrix.getElem_columnTupleMatrix
open _root_.P2MLLL.t19afdfff renaming h19 → _p2mH19
open _root_.P2MLLL.t19afdfff renaming h20 → Hex.Matrix.getElem_columnTupleMatrix_compose_perm
open _root_.P2MLLL.t19afdfff renaming h20 → _p2mH20

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section







set_option autoImplicit true



section

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-! # Strictly-increasing column-tuple enumeration

The Cauchy-Binet sum-of-squares formula needs a Mathlib-free enumeration of the
"essentially distinct" column choices: each strictly increasing length-`n`
selection from `Fin m` represents one orbit of injective ordered tuples under
the action of permutations of `Fin n`. The enumeration below builds these
tuples by appending the new largest element, recursing on a `bound` parameter
that constrains the next entry to be strictly less than `bound`.
-/

















set_option maxRecDepth 8192
/-- Forward characterization: every enumerated tuple is strictly increasing and
its entries are all bounded by the recursion bound. -/
 theorem _root_.P2MLLL.t19afdfff.h93 {m : Nat} :
    ∀ (n bound : Nat) (v : Vector (Fin m) n),
      v ∈ selectedColumnTuplesUpTo m n bound →
        IsStrictlyIncreasingColumnTuple v ∧
          ∀ i : Fin n, v[i].val < bound
  | 0, _, v, hv => by
      simp [selectedColumnTuplesUpTo] at hv
      refine ⟨?_, ?_⟩
      · intro i _ _
        exact i.elim0
      · intro i
        exact i.elim0
  | n + 1, bound, v, hv => by
      rw [selectedColumnTuplesUpTo, List.mem_flatMap] at hv
      rcases hv with ⟨c, hc, hmem⟩
      have hclt : c.val < bound := by
        rw [List.mem_filter] at hc
        simpa using hc.2
      rw [List.mem_map] at hmem
      rcases hmem with ⟨pref, hpref, rfl⟩
      have ih := P2MLLL.t19afdfff.h93 n c.val pref hpref
      refine ⟨?_, ?_⟩
      · -- strict increase of `pref.push c`
        apply _root_.Hex.Matrix.isStrictlyIncreasingColumnTuple_push pref c ih.1
        intro i
        exact ih.2 i
      · -- every entry of `pref.push c` is `< bound`
        intro i
        rcases Nat.lt_succ_iff_lt_or_eq.mp i.isLt with hilt | hieq
        · have hi_eq : i = (⟨i.val, hilt⟩ : Fin n).castSucc := by
            apply Fin.ext; rfl
          rw [hi_eq, _root_.Hex.Matrix.getElem_push_castSucc]
          exact Nat.lt_of_lt_of_le (ih.2 ⟨i.val, hilt⟩) (Nat.le_of_lt hclt)
        · have hi_eq : i = Fin.last n := by
            apply Fin.ext; simpa using hieq
          rw [hi_eq, _root_.Hex.Matrix.getElem_push_last_index]
          exact hclt
open _root_.P2MLLL.t19afdfff renaming h93 → Hex.Matrix.mem_selectedColumnTuplesUpTo_imp
open _root_.P2MLLL.t19afdfff renaming h93 → _p2mH93


set_option maxRecDepth 8192
/-- Backward characterization: every strictly increasing tuple whose entries
are all `< bound` is enumerated by the recursive helper. -/
 theorem _root_.P2MLLL.t19afdfff.h94 {m : Nat} :
    ∀ (n bound : Nat) (v : Vector (Fin m) n),
      IsStrictlyIncreasingColumnTuple v →
        (∀ i : Fin n, v[i].val < bound) →
        v ∈ selectedColumnTuplesUpTo m n bound
  | 0, _, v, _, _ => by
      have hv : v = #v[] := by
        ext i hi
        exact absurd hi (by omega)
      simp [selectedColumnTuplesUpTo, hv]
  | n + 1, bound, v, hsi, hbound => by
      -- factor v as `(v.pop).push v[n]`
      have hpush : (v.pop).push (v[Fin.last n]) = v := by
        have hback : v.back = v[Fin.last n] := by
          simp [Vector.back, Fin.last]
        rw [← hback]
        exact Vector.push_pop_back v
      have hpop_get : ∀ i : Fin n,
          v.pop[i] = v[(⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1))] := by
        intro i
        rcases i with ⟨i, hi⟩
        change v.pop[i]'(by simp; omega) = v[i]'(by omega)
        exact Vector.getElem_pop (h := by simp; omega)
      rw [selectedColumnTuplesUpTo, List.mem_flatMap]
      refine ⟨v[Fin.last n], ?_, ?_⟩
      · -- v[last] is in the filtered finRange
        rw [List.mem_filter]
        refine ⟨List.mem_finRange _, ?_⟩
        simpa using hbound (Fin.last n)
      · rw [List.mem_map]
        refine ⟨v.pop, ?_, hpush⟩
        apply P2MLLL.t19afdfff.h94 n (v[Fin.last n]).val
        · -- pop preserves strict increase
          intro i j hij
          have h1 := hpop_get i
          have h2 := hpop_get j
          have base := hsi
            (⟨i.val, by have := i.isLt; omega⟩ : Fin (n + 1))
            (⟨j.val, by have := j.isLt; omega⟩ : Fin (n + 1)) hij
          rw [← h1, ← h2] at base
          exact base
        · -- bound: pop entries < v[Fin.last n]
          intro i
          have h1 := hpop_get i
          have hilt : i.val < n + 1 := by have := i.isLt; omega
          have hi_lt_last :
              (⟨i.val, hilt⟩ : Fin (n + 1)).val < (Fin.last n).val := by
            have := i.isLt
            simp [Fin.last]
          have base := hsi (⟨i.val, hilt⟩ : Fin (n + 1)) (Fin.last n) hi_lt_last
          rw [← h1] at base
          exact base
open _root_.P2MLLL.t19afdfff renaming h94 → Hex.Matrix.mem_selectionsUpTo
open _root_.P2MLLL.t19afdfff renaming h94 → _p2mH94


set_option maxRecDepth 8192
/-- Public membership characterization: a column tuple lies in
`selectedColumnTuples n m` iff it is strictly increasing. -/
theorem _root_.P2MLLL.t19afdfff.h27 {n m : Nat} (cols : Vector (Fin m) n) :
    cols ∈ selectedColumnTuples n m ↔ IsStrictlyIncreasingColumnTuple cols := by
  refine ⟨?_, ?_⟩
  · intro hmem
    exact (_root_.P2MLLL.t19afdfff.h93 n m cols hmem).1
  · intro hsi
    apply _root_.P2MLLL.t19afdfff.h94 n m cols hsi
    intro i
    exact cols[i].isLt
open _root_.P2MLLL.t19afdfff renaming h27 → Hex.Matrix.mem_selectedColumnTuples_iff
open _root_.P2MLLL.t19afdfff renaming h27 → _p2mH27


set_option maxRecDepth 8192
/-- Strictly increasing column tuples induce injective `Fin n → Fin m` selection
functions, so each enumerated tuple yields an injective `columnTupleVectorFn`. -/
theorem _root_.P2MLLL.t19afdfff.h23 {n m : Nat}
    {cols : Vector (Fin m) n} (hsi : IsStrictlyIncreasingColumnTuple cols) :
    Function.Injective (columnTupleVectorFn cols) := by
  intro i j hij
  -- Either i.val < j.val, j.val < i.val, or i.val = j.val. Strict increase rules out the first two.
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · -- i.val < j.val ⇒ cols[i].val < cols[j].val ⇒ cols[i] ≠ cols[j], contradiction.
    have : cols[i].val < cols[j].val := hsi i j hlt
    exact absurd (congrArg Fin.val hij) (Nat.ne_of_lt this)
  · exact Fin.ext heq
  · have : cols[j].val < cols[i].val := hsi j i hgt
    exact absurd (congrArg Fin.val hij.symm) (Nat.ne_of_lt this)
open _root_.P2MLLL.t19afdfff renaming h23 → Hex.Matrix.isStrictlyIncreasingColumnTuple_injective
open _root_.P2MLLL.t19afdfff renaming h23 → _p2mH23








set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h99 (m : Nat) :
    ∀ (n bound : Nat), (selectedColumnTuplesUpTo m n bound).Nodup
  | 0, _ => by simp [selectedColumnTuplesUpTo]
  | n + 1, bound => by
      rw [selectedColumnTuplesUpTo]
      apply _root_.Hex.Matrix.selectedColumnTuplesUpTo_flatMap_nodup
      · exact (List.nodup_finRange m).filter _
      · intro c _hc
        exact P2MLLL.t19afdfff.h99 m n c.val
open _root_.P2MLLL.t19afdfff renaming h99 → Hex.Matrix.selectedColumnTuplesUpTo_nodup
open _root_.P2MLLL.t19afdfff renaming h99 → _p2mH99




set_option maxRecDepth 8192
/-- The strictly-increasing column-tuple enumeration has no duplicates. -/
theorem _root_.P2MLLL.t19afdfff.h31 {n m : Nat} :
    (selectedColumnTuples n m).Nodup :=
  _root_.P2MLLL.t19afdfff.h99 m n m
open _root_.P2MLLL.t19afdfff renaming h31 → Hex.Matrix.selectedColumnTuples_nodup
open _root_.P2MLLL.t19afdfff renaming h31 → _p2mH31


/-! # Canonical sort and orbit factorization for injective column tuples

For the Cauchy-Binet orbit-grouping argument we need, for every injective
ordered column tuple `cols : Vector (Fin m) n`, a canonical factorization

```
cols[i] = (sortInjTuple cols)[(sortInjPerm cols)[i]]
```

where `sortInjTuple cols` is strictly increasing (i.e. lives in
`selectedColumnTuples n m`) and `sortInjPerm cols` is a permutation of
`Fin n` (i.e. lives in `permutationVectors n`). This gives a bijection
between injective `columnTupleVectors n m` entries and the product
`selectedColumnTuples n m × permutationVectors n`, which lets the orbit
sum group ordered minors by their canonical sorted column choice.

The implementation is rank-based: `sortInjPerm cols i` is the number of
columns in `cols` strictly smaller in value than `cols[i]`. For any
`cols`, this is `< n` because `cols[i]` is never strictly less than
itself; for *injective* `cols`, the rank is moreover a bijection on
`Fin n`. -/







set_option maxRecDepth 8192
/-- The `i`-th value of the sorting permutation is the rank `columnRankNat cols i`
of `cols[i]` (the number of strictly smaller positions). -/
@[grind =] theorem _root_.P2MLLL.t19afdfff.h32 {m n : Nat}
    (cols : Vector (Fin m) n) (i : Fin n) :
    (sortInjPerm cols)[i].val = columnRankNat cols i := by
  simp [sortInjPerm]
open _root_.P2MLLL.t19afdfff renaming h32 → Hex.Matrix.sortInjPerm_getElem_val
open _root_.P2MLLL.t19afdfff renaming h32 → _p2mH32




set_option maxRecDepth 8192
/-- Strict version of `List.countP_mono_left`: a single witness where
`q` holds but `p` doesn't forces strict inequality. -/
 theorem _root_.P2MLLL.t19afdfff.h87 {α : Type u}
    (p q : α → Bool)
    (hle_all : ∀ (xs : List α) (x : α), x ∈ xs → p x = true → q x = true) :
    ∀ (xs : List α) (k : α), k ∈ xs → q k = true → p k = false →
      xs.countP p < xs.countP q
  | [], _k, hkmem, _, _ => by exact absurd hkmem List.not_mem_nil
  | x :: xs, k, hkmem, hqk, hpk => by
      simp only [List.mem_cons] at hkmem
      rcases hkmem with heq | hk_in_xs
      · -- x = k: at the head, `p k = false` and `q k = true`.
        subst heq
        have hxs_le : xs.countP p ≤ xs.countP q :=
          List.countP_mono_left
            (fun y hy => hle_all _ y (List.mem_cons_of_mem k hy))
        simp [hqk, hpk]
        omega
      · -- k ∈ xs: recurse on the tail.
        have ih :=
          P2MLLL.t19afdfff.h87 p q hle_all xs k hk_in_xs hqk hpk
        by_cases hpx : p x = true
        · have hqx : q x = true := hle_all (x :: xs) x List.mem_cons_self hpx
          simp [hpx, hqx]; omega
        · have hpx' : p x = false := by
            cases hpe : p x with
            | true => exact absurd hpe hpx
            | false => rfl
          by_cases hqx : q x = true
          · simp [hpx', hqx]; omega
          · have hqx' : q x = false := by
              cases hqe : q x with
              | true => exact absurd hqe hqx
              | false => rfl
            simp [hpx', hqx']; exact ih
open _root_.P2MLLL.t19afdfff renaming h87 → Hex.Matrix.countP_lt_countP
open _root_.P2MLLL.t19afdfff renaming h87 → _p2mH87


set_option maxRecDepth 8192
/-- Monotonicity of the rank: if `cols[i].val < cols[j].val` then the
rank strictly increases from `i` to `j`. Holds for any `cols`, no
injectivity assumption needed. -/
 theorem _root_.P2MLLL.t19afdfff.h81 {m n : Nat} (cols : Vector (Fin m) n)
    {i j : Fin n} (hij : cols[i].val < cols[j].val) :
    columnRankNat cols i < columnRankNat cols j := by
  -- Switch from `length filter` to `countP`.
  have hlen_eq_p :
      ((List.finRange n).filter fun k => decide (cols[k].val < cols[i].val)).length
        = (List.finRange n).countP (fun k => decide (cols[k].val < cols[i].val)) := by
    rw [List.countP_eq_length_filter]
  have hlen_eq_q :
      ((List.finRange n).filter fun k => decide (cols[k].val < cols[j].val)).length
        = (List.finRange n).countP (fun k => decide (cols[k].val < cols[j].val)) := by
    rw [List.countP_eq_length_filter]
  unfold columnRankNat
  rw [hlen_eq_p, hlen_eq_q]
  -- Strict comparison via element `i`.
  refine _root_.P2MLLL.t19afdfff.h87
    (fun k => decide (cols[k].val < cols[i].val))
    (fun k => decide (cols[k].val < cols[j].val))
    ?_ (List.finRange n) i (List.mem_finRange i)
    (decide_eq_true hij) ?_
  · intro _ k _hkmem hpk
    have hkk : cols[k].val < cols[i].val := by simpa using hpk
    exact decide_eq_true (Nat.lt_trans hkk hij)
  · simp
open _root_.P2MLLL.t19afdfff renaming h81 → Hex.Matrix.columnRankNat_strictMono
open _root_.P2MLLL.t19afdfff renaming h81 → _p2mH81


set_option maxRecDepth 8192
/-- For an injective `cols`, the rank function is itself injective: two
positions with the same rank must agree as `Fin n`. -/
 theorem _root_.P2MLLL.t19afdfff.h78 {m n : Nat}
    (cols : Vector (Fin m) n) (hinj : Function.Injective (columnTupleVectorFn cols)) :
    Function.Injective (columnRankNat cols) := by
  intro i j hrank
  rcases Nat.lt_trichotomy cols[i].val cols[j].val with hlt | heq | hgt
  · exact absurd (_root_.P2MLLL.t19afdfff.h81 cols hlt) (by omega)
  · -- cols[i].val = cols[j].val ⇒ cols[i] = cols[j] ⇒ i = j by injectivity.
    have hcol_eq : cols[i] = cols[j] := Fin.ext heq
    exact hinj hcol_eq
  · exact absurd (_root_.P2MLLL.t19afdfff.h81 cols hgt) (by omega)
open _root_.P2MLLL.t19afdfff renaming h78 → Hex.Matrix.columnRankNat_injective_of_injective
open _root_.P2MLLL.t19afdfff renaming h78 → _p2mH78


set_option maxRecDepth 8192
/-- For an injective `cols`, `sortInjPerm cols` is a permutation as a list. -/
 theorem _root_.P2MLLL.t19afdfff.h101 {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    (sortInjPerm cols).toList.Nodup := by
  rw [_root_.P2MLLL.t19afdfff.h141]
  apply _root_.Hex.Matrix.list_nodup_map_of_injective ?_ (List.nodup_finRange n)
  intro i j hij
  have hval : columnRankNat cols i = columnRankNat cols j := by
    have := congrArg Fin.val hij
    simpa [sortInjPerm] using this
  exact _root_.P2MLLL.t19afdfff.h78 cols hinj hval
open _root_.P2MLLL.t19afdfff renaming h101 → Hex.Matrix.sortInjPerm_toList_nodup
open _root_.P2MLLL.t19afdfff renaming h101 → _p2mH101


set_option maxRecDepth 8192
/-- For an injective `cols`, `sortInjPerm cols ∈ permutationVectors n`. -/
theorem _root_.P2MLLL.t19afdfff.h33 {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    sortInjPerm cols ∈ permutationVectors n :=
  permutationVectors_complete (_root_.P2MLLL.t19afdfff.h101 cols hinj)
open _root_.P2MLLL.t19afdfff renaming h33 → Hex.Matrix.sortInjPerm_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h33 → _p2mH33


set_option maxRecDepth 8192
/-- Converse of `columnRankNat_strictMono` for injective `cols`: a strict
rank comparison implies the underlying value comparison. -/
 theorem _root_.P2MLLL.t19afdfff.h91 {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols))
    {i j : Fin n} (hij : columnRankNat cols i < columnRankNat cols j) :
    cols[i].val < cols[j].val := by
  rcases Nat.lt_trichotomy cols[i].val cols[j].val with hlt | heq | hgt
  · exact hlt
  · have hcol_eq : cols[i] = cols[j] := Fin.ext heq
    have hij' : i = j := hinj hcol_eq
    subst hij'
    omega
  · have := _root_.P2MLLL.t19afdfff.h81 cols hgt
    omega
open _root_.P2MLLL.t19afdfff renaming h91 → Hex.Matrix.get_lt_rank
open _root_.P2MLLL.t19afdfff renaming h91 → _p2mH91


set_option maxRecDepth 8192
/-- `Vector.ofFn`-indexed access at a `Fin n` argument, packaged so that
the result is the function applied to the original `Fin n` index rather
than to its repackaged Nat-value form. -/
 theorem _root_.P2MLLL.t19afdfff.h102 {α : Type u} {n : Nat}
    (f : Fin n → α) (k : Fin n) :
    (Vector.ofFn f)[k] = f k := by
  rw [show ((Vector.ofFn f)[k] : α) = (Vector.ofFn f)[k.val]'(by simp [k.isLt]) from rfl,
    Vector.getElem_ofFn]
open _root_.P2MLLL.t19afdfff renaming h102 → Hex.Matrix.vector_ofFn_getElem_fin
open _root_.P2MLLL.t19afdfff renaming h102 → _p2mH102


set_option maxRecDepth 8192
/-- Every length-`n` tuple of column indices appears in
`columnTupleVectors n m`. -/
theorem _root_.P2MLLL.t19afdfff.h25 {n m : Nat} (cols : Vector (Fin m) n) :
    cols ∈ columnTupleVectors n m := by
  have hcols : cols = Vector.ofFn (fun i : Fin n => cols[i]) := by
    ext i hi
    apply Fin.val_eq_of_eq
    let k : Fin n := ⟨i, hi⟩
    change cols[k] = (Vector.ofFn fun i : Fin n => cols[i])[k]
    rw [_root_.P2MLLL.t19afdfff.h102]
  rw [hcols]
  exact _root_.P2MLLL.t19afdfff.h4 (fun i : Fin n => cols[i])
open _root_.P2MLLL.t19afdfff renaming h25 → Hex.Matrix.mem_columnTupleVectors
open _root_.P2MLLL.t19afdfff renaming h25 → _p2mH25


set_option maxRecDepth 8192
/-- Factorization equation: each entry of `cols` is recovered through the
canonical sort/permutation pair. Requires injectivity of `cols`. -/
theorem _root_.P2MLLL.t19afdfff.h37 {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols))
    (i : Fin n) :
    cols[i] = (sortInjTuple cols)[(sortInjPerm cols)[i]] := by
  have hnodup := _root_.P2MLLL.t19afdfff.h101 cols hinj
  have hidx :=
    _root_.P2MLLL.t19afdfff.h124 (sortInjPerm cols) hnodup i
  have hinv_eq : inversePermutationVector (sortInjPerm cols)
                   = inversePermutationValues (sortInjPerm cols) hnodup :=
    _root_.P2MLLL.t19afdfff.h129 (sortInjPerm cols) hnodup
  have hstep :
      (inversePermutationVector (sortInjPerm cols))[(sortInjPerm cols)[i]]
        = (inversePermutationValues (sortInjPerm cols) hnodup)[(sortInjPerm cols)[i]] :=
    congrArg (fun v : Vector (Fin n) n => v[(sortInjPerm cols)[i]]) hinv_eq
  have hcompose :
      (inversePermutationVector (sortInjPerm cols))[(sortInjPerm cols)[i]] = i :=
    hstep.trans hidx
  rw [sortInjTuple, _root_.P2MLLL.t19afdfff.h102]
  exact (congrArg (fun k : Fin n => cols[k]) hcompose).symm
open _root_.P2MLLL.t19afdfff renaming h37 → Hex.Matrix.sort_reconstruct_get
open _root_.P2MLLL.t19afdfff renaming h37 → _p2mH37


set_option maxRecDepth 8192
/-- For an injective `cols`, applying `sortInjPerm` after the inverse
returns the input rank. -/
 theorem _root_.P2MLLL.t19afdfff.h100 {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) (r : Fin n) :
    (sortInjPerm cols)[(inversePermutationVector (sortInjPerm cols))[r]] = r := by
  have hnodup := _root_.P2MLLL.t19afdfff.h101 cols hinj
  have hval := _root_.P2MLLL.t19afdfff.h125 (sortInjPerm cols) hnodup r
  have hinv_eq : inversePermutationVector (sortInjPerm cols)
                   = inversePermutationValues (sortInjPerm cols) hnodup :=
    _root_.P2MLLL.t19afdfff.h129 (sortInjPerm cols) hnodup
  have hstep :
      (sortInjPerm cols)[(inversePermutationVector (sortInjPerm cols))[r]]
        = (sortInjPerm cols)[(inversePermutationValues (sortInjPerm cols) hnodup)[r]] :=
    congrArg (fun v : Vector (Fin n) n => (sortInjPerm cols)[v[r]]) hinv_eq
  exact hstep.trans hval
open _root_.P2MLLL.t19afdfff renaming h100 → Hex.Matrix.sortInjPerm_inv_apply
open _root_.P2MLLL.t19afdfff renaming h100 → _p2mH100


set_option maxRecDepth 8192
/-- For an injective `cols`, the column-rank at the inverse-perm image
of `r` is exactly `r.val`. -/
 theorem _root_.P2MLLL.t19afdfff.h79 {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) (r : Fin n) :
    columnRankNat cols (inversePermutationVector (sortInjPerm cols))[r] = r.val := by
  have hval' := _root_.P2MLLL.t19afdfff.h100 cols hinj r
  have := congrArg Fin.val hval'
  simpa [sortInjPerm] using this
open _root_.P2MLLL.t19afdfff renaming h79 → Hex.Matrix.columnRankNat_inv_apply
open _root_.P2MLLL.t19afdfff renaming h79 → _p2mH79


set_option maxRecDepth 8192
/-- For an injective `cols`, the canonical sorted tuple is strictly
increasing. -/
theorem _root_.P2MLLL.t19afdfff.h24 {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    IsStrictlyIncreasingColumnTuple (sortInjTuple cols) := by
  intro r r' hrr'
  have hrank_r := _root_.P2MLLL.t19afdfff.h79 cols hinj r
  have hrank_r' := _root_.P2MLLL.t19afdfff.h79 cols hinj r'
  have hrank_lt :
      columnRankNat cols (inversePermutationVector (sortInjPerm cols))[r] <
        columnRankNat cols (inversePermutationVector (sortInjPerm cols))[r'] := by
    rw [hrank_r, hrank_r']; exact hrr'
  have hval_lt :
      cols[(inversePermutationVector (sortInjPerm cols))[r]].val <
        cols[(inversePermutationVector (sortInjPerm cols))[r']].val :=
    _root_.P2MLLL.t19afdfff.h91 cols hinj hrank_lt
  show (sortInjTuple cols)[r].val < (sortInjTuple cols)[r'].val
  rw [sortInjTuple, _root_.P2MLLL.t19afdfff.h102, _root_.P2MLLL.t19afdfff.h102]
  exact hval_lt
open _root_.P2MLLL.t19afdfff renaming h24 → Hex.Matrix.isStrictlyIncreasingColumnTuple_sortInjTuple
open _root_.P2MLLL.t19afdfff renaming h24 → _p2mH24


set_option maxRecDepth 8192
/-- For an injective `cols`, the canonical sorted tuple is enumerated by
`selectedColumnTuples n m`. -/
theorem _root_.P2MLLL.t19afdfff.h35 {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    sortInjTuple cols ∈ selectedColumnTuples n m :=
  (_root_.P2MLLL.t19afdfff.h27 (sortInjTuple cols)).mpr
    (_root_.P2MLLL.t19afdfff.h24 cols hinj)
open _root_.P2MLLL.t19afdfff renaming h35 → Hex.Matrix.sortInjTuple_mem_selectedColumnTuples
open _root_.P2MLLL.t19afdfff renaming h35 → _p2mH35


/-! # Forward injectivity of the sort/permutation pair -/



/-! # Reconstruction from `selectedColumnTuples × permutationVectors`

For a strictly-increasing `sel` and a permutation `perm`, the
"reconstruction" `Vector.ofFn (fun i => sel[perm[i]])` is itself
injective, and its canonical sort/permutation pair recovers
`(sel, perm)`. This is the inverse map of `sortInjTuple`/`sortInjPerm`. -/



set_option maxRecDepth 8192
/-- The `i`-th entry of the reconstructed tuple is `sel[perm[i]]`: read the
sorted choice `sel` through the permutation `perm`. -/
@[grind =] theorem _root_.P2MLLL.t19afdfff.h21 {m n : Nat}
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) (i : Fin n) :
    (reconstructInjTuple sel perm)[i] = sel[perm[i]] := by
  rw [reconstructInjTuple, _root_.P2MLLL.t19afdfff.h102]
open _root_.P2MLLL.t19afdfff renaming h21 → Hex.Matrix.getElem_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h21 → _p2mH21




set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h85
    {R : Type u} {n m : Nat} (A : Matrix R n m)
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) :
    columnTupleMatrix A (columnTupleVectorFn (reconstructInjTuple sel perm)) =
      columnTupleMatrix A (fun i => sel[perm[i]]) := by
  ext r hr c hc
  simp only [getElem_rows]
  change
    (columnTupleMatrix A (columnTupleVectorFn (reconstructInjTuple sel perm)))[
        (⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)] =
      (columnTupleMatrix A (fun i => sel[perm[i]]))[(⟨r, hr⟩ : Fin n)][(⟨c, hc⟩ : Fin n)]
  rw [_root_.P2MLLL.t19afdfff.h19, _root_.P2MLLL.t19afdfff.h19]
  exact congrArg (fun col : Fin m => A[(⟨r, hr⟩ : Fin n)][col])
    (_root_.P2MLLL.t19afdfff.h21 sel perm (⟨c, hc⟩ : Fin n))
open _root_.P2MLLL.t19afdfff renaming h85 → Hex.Matrix.columnTupleMatrix_reconstructInjTuple_eq
open _root_.P2MLLL.t19afdfff renaming h85 → _p2mH85


set_option maxRecDepth 8192
/-- Reconstructing an injective tuple from a selected tuple and a permutation
turns the coefficient product into the corresponding determinant product. -/
theorem _root_.P2MLLL.t19afdfff.h0
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) :
    columnTupleCoeff A (reconstructInjTuple sel perm) =
      detProduct (columnTupleMatrix A (columnTupleVectorFn sel)) perm := by
  unfold columnTupleCoeff detProduct
  simp only [Fin.foldl_eq_finRange_foldl]
  apply _root_.P2MLLL.t19afdfff.h46
  intro i _hmem
  simp only [getElem_pair_eq_nested]
  rw [_root_.P2MLLL.t19afdfff.h19]
  exact congrArg (fun col : Fin m => A[i][col])
    (_root_.P2MLLL.t19afdfff.h21 sel perm i)
open _root_.P2MLLL.t19afdfff renaming h0 → Hex.Matrix.columnTupleCoeff_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h0 → _p2mH0


set_option maxRecDepth 8192
/-- Counting how many entries of `List.finRange n` have value `< k`. -/
 theorem _root_.P2MLLL.t19afdfff.h86 :
    ∀ (n k : Nat), (List.finRange n).countP (fun x : Fin n => decide (x.val < k)) = min n k
  | 0, k => by simp
  | n + 1, k => by
      rw [List.finRange_succ_last, List.countP_append, List.countP_map]
      -- The induction hypothesis applies to the `map Fin.castSucc` part.
      -- `(castSucc x).val = x.val`, so the composed predicate matches.
      have ih := P2MLLL.t19afdfff.h86 n k
      have hmap_eq :
          (List.finRange n).countP ((fun x : Fin (n + 1) => decide (x.val < k)) ∘ Fin.castSucc) =
            (List.finRange n).countP (fun x : Fin n => decide (x.val < k)) := rfl
      rw [hmap_eq, ih]
      -- Singleton contribution.
      simp only [List.countP_singleton, Fin.last]
      -- Goal: min n k + (if decide (n < k) then 1 else 0) = min (n+1) k.
      by_cases hnk : n < k
      · rw [if_pos (by simpa using hnk)]
        omega
      · rw [if_neg (by simpa using hnk)]
        omega
open _root_.P2MLLL.t19afdfff renaming h86 → Hex.Matrix.countP_finRange_val_lt
open _root_.P2MLLL.t19afdfff renaming h86 → _p2mH86


set_option maxRecDepth 8192
/-- A permutation as a `Vector` acts as an injective function on `Fin n`. -/
 theorem _root_.P2MLLL.t19afdfff.h96 {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    Function.Injective (fun i : Fin n => perm[i]) := by
  intro i j hij
  have hnodup := permutationVectors_nodup hmem
  -- Apply the inverse-permutation to both sides.
  have hstep :
      (inversePermutationValues perm hnodup)[perm[i]]
        = (inversePermutationValues perm hnodup)[perm[j]] :=
    congrArg (fun k : Fin n => (inversePermutationValues perm hnodup)[k]) hij
  have hi := _root_.P2MLLL.t19afdfff.h124 perm hnodup i
  have hj := _root_.P2MLLL.t19afdfff.h124 perm hnodup j
  exact hi.symm.trans (hstep.trans hj)
open _root_.P2MLLL.t19afdfff renaming h96 → Hex.Matrix.permutationVectors_getElem_injective
open _root_.P2MLLL.t19afdfff renaming h96 → _p2mH96


set_option maxRecDepth 8192
/-- The reconstructed column tuple is itself injective when `sel` is
strictly increasing and `perm` is a permutation. -/
theorem _root_.P2MLLL.t19afdfff.h28 {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) :
    Function.Injective (columnTupleVectorFn (reconstructInjTuple sel perm)) := by
  intro i j hij
  have hsel_inj := _root_.P2MLLL.t19afdfff.h23 hsel
  have hperm_inj := _root_.P2MLLL.t19afdfff.h96 hperm
  -- `hij` is equality of reconstructed entries; extract `sel[perm[i]] = sel[perm[j]]`.
  have hval : sel[perm[i]] = sel[perm[j]] := by
    have hi := _root_.P2MLLL.t19afdfff.h21 sel perm i
    have hj := _root_.P2MLLL.t19afdfff.h21 sel perm j
    have hij' :
        (reconstructInjTuple sel perm)[i] = (reconstructInjTuple sel perm)[j] := hij
    exact hi.symm.trans (hij'.trans hj)
  exact hperm_inj (hsel_inj hval)
open _root_.P2MLLL.t19afdfff renaming h28 → Hex.Matrix.reconstructInjTuple_injective
open _root_.P2MLLL.t19afdfff renaming h28 → _p2mH28


set_option maxRecDepth 8192
/-- For a strictly-increasing `sel`, value comparison agrees with index
comparison. -/
 theorem _root_.P2MLLL.t19afdfff.h92 {m n : Nat}
    {sel : Vector (Fin m) n} (hsel : IsStrictlyIncreasingColumnTuple sel)
    (a b : Fin n) :
    sel[a].val < sel[b].val ↔ a.val < b.val := by
  refine ⟨?_, hsel a b⟩
  intro hlt
  rcases Nat.lt_trichotomy a.val b.val with hltab | heqab | hgtab
  · exact hltab
  · have : a = b := Fin.ext heqab
    subst this; omega
  · have := hsel b a hgtab; omega
open _root_.P2MLLL.t19afdfff renaming h92 → Hex.Matrix.isStrictlyIncreasingColumnTuple_val_lt_iff
open _root_.P2MLLL.t19afdfff renaming h92 → _p2mH92


set_option maxRecDepth 8192
/-- For a permutation `perm`, the `toList` is a `List.Perm` of `List.finRange n`. -/
 theorem _root_.P2MLLL.t19afdfff.h98 {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    perm.toList.Perm (List.finRange n) := by
  have hnodup := permutationVectors_nodup hmem
  apply (List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)).mpr
  intro x
  refine ⟨fun _ => List.mem_finRange x, fun _ => ?_⟩
  exact _root_.Hex.Matrix.fin_mem_of_full_nodup x (by simp [Vector.length_toList]) hnodup
open _root_.P2MLLL.t19afdfff renaming h98 → Hex.Matrix.permutationVectors_toList_perm_finRange
open _root_.P2MLLL.t19afdfff renaming h98 → _p2mH98


set_option maxRecDepth 8192
/-- Count of indices `j` for which `perm[j].val < k.val` is exactly `k.val`
when `perm` is a permutation. -/
 theorem _root_.P2MLLL.t19afdfff.h95 {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) (k : Fin n) :
    (List.finRange n).countP (fun j : Fin n => decide (perm[j].val < k.val)) = k.val := by
  -- Reduce to counting on perm.toList via `countP_map`.
  have hmap :
      (List.finRange n).countP (fun j : Fin n => decide (perm[j].val < k.val)) =
        ((List.finRange n).map fun j : Fin n => perm[j]).countP
          (fun x : Fin n => decide (x.val < k.val)) := by
    rw [List.countP_map]
    rfl
  have htoList : perm.toList = (List.finRange n).map (fun j : Fin n => perm[j]) :=
    _root_.P2MLLL.t19afdfff.h141 perm
  rw [hmap, ← htoList, List.Perm.countP_eq _ (_root_.P2MLLL.t19afdfff.h98 hmem),
    _root_.P2MLLL.t19afdfff.h86]
  exact Nat.min_eq_right (Nat.le_of_lt k.isLt)
open _root_.P2MLLL.t19afdfff renaming h95 → Hex.Matrix.permutationVectors_count_val_lt
open _root_.P2MLLL.t19afdfff renaming h95 → _p2mH95


set_option maxRecDepth 8192
/-- For a strictly-increasing `sel` and a permutation `perm`, the column
rank of the reconstruction at index `i` agrees with `perm[i].val`. -/
 theorem _root_.P2MLLL.t19afdfff.h80 {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) (i : Fin n) :
    columnRankNat (reconstructInjTuple sel perm) i = (perm[i]).val := by
  unfold columnRankNat
  -- Convert filter to countP, replace predicate using strict monotonicity, then
  -- apply the permutation count lemma.
  rw [← List.countP_eq_length_filter]
  have hpred :
      (fun j : Fin n => decide ((reconstructInjTuple sel perm)[j].val
                                   < (reconstructInjTuple sel perm)[i].val)) =
        (fun j : Fin n => decide ((perm[j]).val < (perm[i]).val)) := by
    funext j
    rw [_root_.P2MLLL.t19afdfff.h21, _root_.P2MLLL.t19afdfff.h21]
    exact decide_eq_decide.mpr (_root_.P2MLLL.t19afdfff.h92 hsel _ _)
  rw [hpred]
  exact _root_.P2MLLL.t19afdfff.h95 hperm (perm[i])
open _root_.P2MLLL.t19afdfff renaming h80 → Hex.Matrix.columnRankNat_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h80 → _p2mH80


set_option maxRecDepth 8192
/-- `sortInjPerm` of a reconstructed tuple recovers the original permutation. -/
theorem _root_.P2MLLL.t19afdfff.h34 {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) :
    sortInjPerm (reconstructInjTuple sel perm) = perm := by
  ext k hk
  apply Fin.val_eq_of_eq
  let i : Fin n := ⟨k, hk⟩
  show (sortInjPerm (reconstructInjTuple sel perm))[i] = perm[i]
  apply Fin.ext
  rw [_root_.P2MLLL.t19afdfff.h32]
  exact _root_.P2MLLL.t19afdfff.h80 hsel hperm i
open _root_.P2MLLL.t19afdfff renaming h34 → Hex.Matrix.sortInjPerm_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h34 → _p2mH34


set_option maxRecDepth 8192
/-- `sortInjTuple` of a reconstructed tuple recovers the original selection. -/
theorem _root_.P2MLLL.t19afdfff.h36 {m n : Nat}
    {sel : Vector (Fin m) n} {perm : Vector (Fin n) n}
    (hsel : IsStrictlyIncreasingColumnTuple sel)
    (hperm : perm ∈ permutationVectors n) :
    sortInjTuple (reconstructInjTuple sel perm) = sel := by
  -- Use the factorization equation on the reconstructed tuple, which is injective.
  have hinj : Function.Injective (columnTupleVectorFn (reconstructInjTuple sel perm)) :=
    _root_.P2MLLL.t19afdfff.h28 hsel hperm
  ext k hk
  apply Fin.val_eq_of_eq
  let r : Fin n := ⟨k, hk⟩
  show (sortInjTuple (reconstructInjTuple sel perm))[r] = sel[r]
  -- The reconstruction at index `inv perm [r]` equals sel[perm[(inv perm) r]] = sel[r].
  -- And by the factorization equation, this equals sortInjTuple cols at sortInjPerm cols [(inv perm) r]
  -- which is just r by the permutation identity. Hmm, this is circular.
  -- Direct: sortInjTuple cols [r] = cols[inv (sortInjPerm cols) [r]]
  --                                = cols[inv perm [r]]                    -- by sortInjPerm_reconstructInjTuple
  --                                = sel[perm[(inv perm) r]]               -- by reconstruction defn
  --                                = sel[r]                                -- by perm ∘ inv perm = id
  have hsortPerm := _root_.P2MLLL.t19afdfff.h34 hsel hperm
  -- Substitute sortInjPerm with perm in the sortInjTuple definition.
  rw [sortInjTuple, _root_.P2MLLL.t19afdfff.h102]
  -- Goal: cols[inv (sortInjPerm cols) [r]] = sel[r]
  -- where cols := reconstructInjTuple sel perm.
  have hinv_eq : inversePermutationVector (sortInjPerm (reconstructInjTuple sel perm))
                   = inversePermutationVector perm :=
    congrArg inversePermutationVector hsortPerm
  have hstep :
      (reconstructInjTuple sel perm)[(inversePermutationVector
                                        (sortInjPerm (reconstructInjTuple sel perm)))[r]]
        = (reconstructInjTuple sel perm)[(inversePermutationVector perm)[r]] :=
    congrArg
      (fun v : Vector (Fin n) n => (reconstructInjTuple sel perm)[v[r]])
      hinv_eq
  rw [hstep]
  -- Now: reconstruction at (inv perm)[r] = sel[perm[(inv perm)[r]]] = sel[r].
  rw [_root_.P2MLLL.t19afdfff.h21]
  -- Use that perm ∘ inv perm = id (i.e., perm[(inv perm)[r]] = r).
  have hnodup := permutationVectors_nodup hperm
  have hinv_perm : inversePermutationVector perm
                     = inversePermutationValues perm hnodup :=
    _root_.P2MLLL.t19afdfff.h129 perm hnodup
  have hval := _root_.P2MLLL.t19afdfff.h125 perm hnodup r
  -- hval : perm[(inv perm) [r]] = r (where inv perm = inversePermutationValues perm hnodup)
  have hstep' :
      perm[(inversePermutationVector perm)[r]]
        = perm[(inversePermutationValues perm hnodup)[r]] :=
    congrArg (fun v : Vector (Fin n) n => perm[v[r]]) hinv_perm
  have hperm_apply : perm[(inversePermutationVector perm)[r]] = r := hstep'.trans hval
  -- Therefore: sel[perm[(inv perm)[r]]] = sel[r] via congrArg.
  exact congrArg (fun k : Fin n => sel[k]) hperm_apply
open _root_.P2MLLL.t19afdfff renaming h36 → Hex.Matrix.sortInjTuple_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h36 → _p2mH36


/-! # Bijection wrappers -/

set_option maxRecDepth 8192
/-- Forward-then-backward identity: reconstruction inverts the canonical
sort/permutation pair on injective column tuples. -/
theorem _root_.P2MLLL.t19afdfff.h29 {m n : Nat}
    (cols : Vector (Fin m) n)
    (hinj : Function.Injective (columnTupleVectorFn cols)) :
    reconstructInjTuple (sortInjTuple cols) (sortInjPerm cols) = cols := by
  ext k hk
  apply Fin.val_eq_of_eq
  let i : Fin n := ⟨k, hk⟩
  show (reconstructInjTuple (sortInjTuple cols) (sortInjPerm cols))[i] = cols[i]
  rw [_root_.P2MLLL.t19afdfff.h21]
  exact (_root_.P2MLLL.t19afdfff.h37 cols hinj i).symm
open _root_.P2MLLL.t19afdfff renaming h29 → Hex.Matrix.reconstructInjTuple_sortInj
open _root_.P2MLLL.t19afdfff renaming h29 → _p2mH29


set_option maxRecDepth 8192
/-- For each fixed `sel`, the inner `map (reconstructInjTuple sel)` list
is `Nodup` over `permutationVectors n`. -/
 theorem _root_.P2MLLL.t19afdfff.h97 {m n : Nat}
    {sel : Vector (Fin m) n} (hsel : IsStrictlyIncreasingColumnTuple sel) :
    ((permutationVectors n).map (reconstructInjTuple sel)).Nodup := by
  apply _root_.Hex.Matrix.list_nodup_map_on permutationVectors_nodup_list
  intro a ha b hb hab
  -- Apply sortInjPerm to both sides to recover the permutation.
  have := congrArg sortInjPerm hab
  rw [_root_.P2MLLL.t19afdfff.h34 hsel ha,
      _root_.P2MLLL.t19afdfff.h34 hsel hb] at this
  exact this
open _root_.P2MLLL.t19afdfff renaming h97 → Hex.Matrix.permutationVectors_map_reconstruct_nodup
open _root_.P2MLLL.t19afdfff renaming h97 → _p2mH97


set_option maxRecDepth 8192
/-- The flat list of reconstructed column tuples, indexed by
`selectedColumnTuples × permutationVectors`, has no duplicates. -/
theorem _root_.P2MLLL.t19afdfff.h30 {m n : Nat} :
    ((selectedColumnTuples n m).flatMap fun sel =>
      (permutationVectors n).map (reconstructInjTuple sel)).Nodup := by
  -- Generalize so we can induct on the outer list (selectedColumnTuples).
  suffices h : ∀ (sels : List (Vector (Fin m) n)), sels.Nodup →
      (∀ sel ∈ sels, IsStrictlyIncreasingColumnTuple sel) →
      (sels.flatMap fun sel =>
        (permutationVectors n).map (reconstructInjTuple sel)).Nodup by
    exact h _ _root_.P2MLLL.t19afdfff.h31
      (fun sel hmem => (_root_.P2MLLL.t19afdfff.h27 sel).mp hmem)
  intro sels hsels_nodup hsels_inc
  induction sels with
  | nil => simp
  | cons s ss ih =>
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      simp only [List.nodup_cons] at hsels_nodup
      refine ⟨?_, ?_, ?_⟩
      · -- Inner head list is Nodup.
        exact _root_.P2MLLL.t19afdfff.h97 (hsels_inc s (by simp))
      · -- Tail Nodup by IH.
        exact ih hsels_nodup.2 (fun sel' hsel' => hsels_inc sel' (List.mem_cons_of_mem s hsel'))
      · -- Disjointness: a reconstruction with `sel = s` and a reconstruction
        -- with `sel = s' ∈ ss` agree only if `s = s'` by `sortInjTuple`.
        intro a ha_head b hb_suffix hab
        rcases List.mem_map.mp ha_head with ⟨perm, hperm_mem, rfl⟩
        rcases List.mem_flatMap.mp hb_suffix with ⟨s', hs'_mem, hb_in⟩
        rcases List.mem_map.mp hb_in with ⟨perm', hperm'_mem, hb_eq⟩
        -- hab : (reconstructInjTuple s perm) = b; hb_eq : reconstructInjTuple s' perm' = b
        have hrec_eq : reconstructInjTuple s perm = reconstructInjTuple s' perm' :=
          hab.trans hb_eq.symm
        have hs_inc := hsels_inc s (by simp)
        have hs'_inc := hsels_inc s' (List.mem_cons_of_mem s hs'_mem)
        have hsort := congrArg sortInjTuple hrec_eq
        rw [_root_.P2MLLL.t19afdfff.h36 hs_inc hperm_mem,
            _root_.P2MLLL.t19afdfff.h36 hs'_inc hperm'_mem] at hsort
        subst hsort
        exact hsels_nodup.1 hs'_mem
open _root_.P2MLLL.t19afdfff renaming h30 → Hex.Matrix.selPerm_reconstructed_list_nodup
open _root_.P2MLLL.t19afdfff renaming h30 → _p2mH30


set_option maxRecDepth 8192
/-- A column tuple is injective iff it is enumerated by the
`selectedColumnTuples × permutationVectors` reconstruction. This is the
bijection statement in membership form. -/
theorem _root_.P2MLLL.t19afdfff.h26 {m n : Nat} (cols : Vector (Fin m) n) :
    cols ∈ ((selectedColumnTuples n m).flatMap fun sel =>
      (permutationVectors n).map (reconstructInjTuple sel)) ↔
      Function.Injective (columnTupleVectorFn cols) := by
  refine ⟨?_, ?_⟩
  · -- Backward: every reconstruction is injective.
    intro hmem
    rcases List.mem_flatMap.mp hmem with ⟨sel, hsel_mem, hinner⟩
    rcases List.mem_map.mp hinner with ⟨perm, hperm_mem, rfl⟩
    have hsel_inc : IsStrictlyIncreasingColumnTuple sel :=
      (_root_.P2MLLL.t19afdfff.h27 sel).mp hsel_mem
    exact _root_.P2MLLL.t19afdfff.h28 hsel_inc hperm_mem
  · -- Forward: every injective tuple is in the reconstruction list, via
    -- (sortInjTuple cols, sortInjPerm cols).
    intro hinj
    rw [List.mem_flatMap]
    refine ⟨sortInjTuple cols, _root_.P2MLLL.t19afdfff.h35 cols hinj, ?_⟩
    rw [List.mem_map]
    refine ⟨sortInjPerm cols, _root_.P2MLLL.t19afdfff.h33 cols hinj, ?_⟩
    exact _root_.P2MLLL.t19afdfff.h29 cols hinj
open _root_.P2MLLL.t19afdfff renaming h26 → Hex.Matrix.mem_selPerm_reconstructed_iff
open _root_.P2MLLL.t19afdfff renaming h26 → _p2mH26


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h88 {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (p : β → Prop) [DecidablePred p]
    (f : β → R) (z : R)
    (hzero : ∀ x, x ∈ xs → ¬ p x → f x = 0) :
    xs.foldl (fun acc x => acc + f x) z =
      (xs.filter p).foldl (fun acc x => acc + f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : p x
      · simp [List.filter, hx]
        apply ih
        intro y hy hpy
        exact hzero y (List.mem_cons_of_mem x hy) hpy
      · simp [List.filter, hx]
        have hxzero : f x = 0 := hzero x (by simp) hx
        rw [hxzero]
        have hacc : z + (0 : R) = z := by grind
        rw [hacc]
        apply ih
        intro y hy hpy
        exact hzero y (List.mem_cons_of_mem x hy) hpy
open _root_.P2MLLL.t19afdfff renaming h88 → Hex.Matrix.foldl_filter_zero
open _root_.P2MLLL.t19afdfff renaming h88 → _p2mH88


set_option maxRecDepth 8192
/-- Refold the ordered column-tuple Gram expansion over the canonical
`selectedColumnTuples × permutationVectors` reconstruction list. Non-injective
ordered tuples contribute zero determinants, and the remaining injective tuples
are exactly the reconstructed selected/permutation tuples. -/
theorem _root_.P2MLLL.t19afdfff.h1
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    (columnTupleVectors n m).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 =
      (((selectedColumnTuples n m).flatMap fun sel =>
          (permutationVectors n).map (reconstructInjTuple sel))).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := by
  classical
  let reconstructed :=
    (selectedColumnTuples n m).flatMap fun sel =>
      (permutationVectors n).map (reconstructInjTuple sel)
  let term := columnTupleExpansionTerm A
  have hfilter :
      (columnTupleVectors n m).foldl (fun acc cols => acc + term cols) 0 =
        ((columnTupleVectors n m).filter
          (fun cols => Function.Injective (columnTupleVectorFn cols))).foldl
            (fun acc cols => acc + term cols) 0 := by
    apply _root_.P2MLLL.t19afdfff.h88
    intro cols hmem hnot
    unfold term columnTupleExpansionTerm
    have hdet :
        det (columnTupleMatrix A (columnTupleVectorFn cols)) = 0 :=
      _root_.P2MLLL.t19afdfff.h11 A (columnTupleVectorFn cols) hnot
    rw [hdet]
    grind
  have hperm :
      ((columnTupleVectors n m).filter
          (fun cols => Function.Injective (columnTupleVectorFn cols))).Perm
        reconstructed := by
    apply (List.perm_ext_iff_of_nodup
      ((_root_.P2MLLL.t19afdfff.h55 (n := n) (m := m)).filter _)
      (by simpa [reconstructed] using (_root_.P2MLLL.t19afdfff.h30 (m := m) (n := n)))).mpr
    intro cols
    constructor
    · intro hmem
      rw [List.mem_filter] at hmem
      exact (_root_.P2MLLL.t19afdfff.h26 cols).mpr (of_decide_eq_true hmem.2)
    · intro hmem
      rw [List.mem_filter]
      exact ⟨_root_.P2MLLL.t19afdfff.h25 cols,
        decide_eq_true ((_root_.P2MLLL.t19afdfff.h26 cols).mp hmem)⟩
  calc
    (columnTupleVectors n m).foldl (fun acc cols => acc + columnTupleExpansionTerm A cols) 0
        = (columnTupleVectors n m).foldl (fun acc cols => acc + term cols) 0 := rfl
    _ = ((columnTupleVectors n m).filter
          (fun cols => Function.Injective (columnTupleVectorFn cols))).foldl
            (fun acc cols => acc + term cols) 0 := hfilter
    _ = reconstructed.foldl (fun acc cols => acc + term cols) 0 := by
          exact _root_.P2MLLL.t19afdfff.h44 term hperm 0
    _ = (((selectedColumnTuples n m).flatMap fun sel =>
          (permutationVectors n).map (reconstructInjTuple sel))).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := rfl
open _root_.P2MLLL.t19afdfff renaming h1 → Hex.Matrix.columnTupleExpansion_refold_selectedPerm
open _root_.P2MLLL.t19afdfff renaming h1 → _p2mH1


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h82
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (sel : Vector (Fin m) n) (perm : Vector (Fin n) n)
    (hperm : perm ∈ permutationVectors n) :
    columnTupleExpansionTerm A (reconstructInjTuple sel perm) =
      detTerm (columnTupleMatrix A (columnTupleVectorFn sel)) perm *
        det (columnTupleMatrix A (columnTupleVectorFn sel)) := by
  unfold columnTupleExpansionTerm detTerm
  rw [_root_.P2MLLL.t19afdfff.h0, _root_.P2MLLL.t19afdfff.h85 A sel perm,
    _root_.P2MLLL.t19afdfff.h9 A sel perm hperm]
  grind
open _root_.P2MLLL.t19afdfff renaming h82 → Hex.Matrix.columnTupleExpansionTerm_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h82 → _p2mH82


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h83
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (A : Matrix R n m) (sel : Vector (Fin m) n) :
    (permutationVectors n).foldl
        (fun acc perm => acc + columnTupleExpansionTerm A (reconstructInjTuple sel perm)) 0 =
      det (columnTupleMatrix A (columnTupleVectorFn sel)) ^ 2 := by
  let minor := columnTupleMatrix A (columnTupleVectorFn sel)
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + columnTupleExpansionTerm A (reconstructInjTuple sel perm)) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + detTerm minor perm * det minor) 0 := by
        apply List.foldl_add_congr
        intro perm hperm
        exact _root_.P2MLLL.t19afdfff.h82 A sel perm hperm
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm minor perm) 0 *
        det minor := by
        exact _root_.P2MLLL.t19afdfff.h43 (permutationVectors n) (fun perm => detTerm minor perm)
          (det minor)
    _ = det minor ^ 2 := by
        unfold det
        grind
open _root_.P2MLLL.t19afdfff renaming h83 → Hex.Matrix.columnTupleExpansion_reconstruct_orbit_sum
open _root_.P2MLLL.t19afdfff renaming h83 → _p2mH83


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h84
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    (((selectedColumnTuples n m).flatMap fun sel =>
        (permutationVectors n).map (reconstructInjTuple sel))).foldl
      (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 =
    (selectedColumnTuples n m).foldl
      (fun acc sel => acc + det (columnTupleMatrix A (columnTupleVectorFn sel)) ^ 2) 0 := by
  rw [_root_.P2MLLL.t19afdfff.h40]
  apply List.foldl_congr
  intro acc sel _hsel
  rw [_root_.P2MLLL.t19afdfff.h39]
  congr 1
  rw [_root_.P2MLLL.t19afdfff.h144, _root_.P2MLLL.t19afdfff.h83 A sel]
open _root_.P2MLLL.t19afdfff renaming h84 → Hex.Matrix.columnTupleExpansion_selectedPerm_collapse
open _root_.P2MLLL.t19afdfff renaming h84 → _p2mH84


/-! # General rectangular Cauchy--Binet -/

























set_option maxRecDepth 8192
/-- Cauchy-Binet for the row Gram matrix: the Gram determinant is the finite
sum of squares of the selected column minors. -/
theorem _root_.P2MLLL.t19afdfff.h14
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat} (A : Matrix R n m) :
    det (gramMatrix A) =
      (selectedColumnTuples n m).foldl
        (fun acc cols => acc + det (columnTupleMatrix A (columnTupleVectorFn cols)) ^ 2) 0 := by
  calc
    det (gramMatrix A) =
      (columnTupleVectors n m).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := by
        exact _root_.P2MLLL.t19afdfff.h13 A
    _ =
      (((selectedColumnTuples n m).flatMap fun sel =>
          (permutationVectors n).map (reconstructInjTuple sel))).foldl
        (fun acc cols => acc + columnTupleExpansionTerm A cols) 0 := by
        exact _root_.P2MLLL.t19afdfff.h1 A
    _ =
      (selectedColumnTuples n m).foldl
        (fun acc cols => acc + det (columnTupleMatrix A (columnTupleVectorFn cols)) ^ 2) 0 := by
        exact _root_.P2MLLL.t19afdfff.h84 A
open _root_.P2MLLL.t19afdfff renaming h14 → Hex.Matrix.det_gram_sum_sq
open _root_.P2MLLL.t19afdfff renaming h14 → _p2mH14


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h90 {β : Type v}
    (xs : List β) (f : β → Int) (acc : Int) (hacc : 0 ≤ acc) :
    0 ≤ xs.foldl (fun acc x => acc + f x ^ 2) acc := by
  induction xs generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : 0 ≤ f x ^ 2 := by
        simpa [Lean.Grind.Semiring.pow_two] using
          (Lean.Grind.OrderedRing.sq_nonneg (a := f x))
      exact ih (acc + f x ^ 2) (Int.add_nonneg hacc hx)
open _root_.P2MLLL.t19afdfff renaming h90 → Hex.Matrix.foldl_sq_nonneg_start
open _root_.P2MLLL.t19afdfff renaming h90 → _p2mH90


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t19afdfff.h89 {β : Type v} (xs : List β) (f : β → Int) :
    0 ≤ xs.foldl (fun acc x => acc + f x ^ 2) 0 :=
  _root_.P2MLLL.t19afdfff.h90 xs f 0 (by simp)
open _root_.P2MLLL.t19afdfff renaming h89 → Hex.Matrix.foldl_sq_nonneg
open _root_.P2MLLL.t19afdfff renaming h89 → _p2mH89








set_option maxRecDepth 8192
/-- Integer row Gram determinants are nonnegative, by Cauchy-Binet as a finite
sum of integer squares. -/
theorem _root_.Hex.Matrix.__p2m_proof_19afdfff033044c5b8d3 {n m : Nat} (A : Matrix Int n m) :
    0 ≤ det (gramMatrix A) := by
  rw [_root_.P2MLLL.t19afdfff.h14 A]
  exact _root_.P2MLLL.t19afdfff.h89 (selectedColumnTuples n m)
    (fun cols => det (columnTupleMatrix A (columnTupleVectorFn cols)))












end Matrix
open _root_.P2MLLL.t19afdfff renaming h0 → Hex.Matrix.columnTupleCoeff_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h0 → _p2mH0
open _root_.P2MLLL.t19afdfff renaming h1 → Hex.Matrix.columnTupleExpansion_refold_selectedPerm
open _root_.P2MLLL.t19afdfff renaming h1 → _p2mH1
open _root_.P2MLLL.t19afdfff renaming h14 → Hex.Matrix.det_gram_sum_sq
open _root_.P2MLLL.t19afdfff renaming h14 → _p2mH14
open _root_.P2MLLL.t19afdfff renaming h21 → Hex.Matrix.getElem_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h21 → _p2mH21
open _root_.P2MLLL.t19afdfff renaming h23 → Hex.Matrix.isStrictlyIncreasingColumnTuple_injective
open _root_.P2MLLL.t19afdfff renaming h23 → _p2mH23
open _root_.P2MLLL.t19afdfff renaming h24 → Hex.Matrix.isStrictlyIncreasingColumnTuple_sortInjTuple
open _root_.P2MLLL.t19afdfff renaming h24 → _p2mH24
open _root_.P2MLLL.t19afdfff renaming h25 → Hex.Matrix.mem_columnTupleVectors
open _root_.P2MLLL.t19afdfff renaming h25 → _p2mH25
open _root_.P2MLLL.t19afdfff renaming h26 → Hex.Matrix.mem_selPerm_reconstructed_iff
open _root_.P2MLLL.t19afdfff renaming h26 → _p2mH26
open _root_.P2MLLL.t19afdfff renaming h27 → Hex.Matrix.mem_selectedColumnTuples_iff
open _root_.P2MLLL.t19afdfff renaming h27 → _p2mH27
open _root_.P2MLLL.t19afdfff renaming h28 → Hex.Matrix.reconstructInjTuple_injective
open _root_.P2MLLL.t19afdfff renaming h28 → _p2mH28
open _root_.P2MLLL.t19afdfff renaming h29 → Hex.Matrix.reconstructInjTuple_sortInj
open _root_.P2MLLL.t19afdfff renaming h29 → _p2mH29
open _root_.P2MLLL.t19afdfff renaming h30 → Hex.Matrix.selPerm_reconstructed_list_nodup
open _root_.P2MLLL.t19afdfff renaming h30 → _p2mH30
open _root_.P2MLLL.t19afdfff renaming h31 → Hex.Matrix.selectedColumnTuples_nodup
open _root_.P2MLLL.t19afdfff renaming h31 → _p2mH31
open _root_.P2MLLL.t19afdfff renaming h32 → Hex.Matrix.sortInjPerm_getElem_val
open _root_.P2MLLL.t19afdfff renaming h32 → _p2mH32
open _root_.P2MLLL.t19afdfff renaming h33 → Hex.Matrix.sortInjPerm_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h33 → _p2mH33
open _root_.P2MLLL.t19afdfff renaming h34 → Hex.Matrix.sortInjPerm_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h34 → _p2mH34
open _root_.P2MLLL.t19afdfff renaming h35 → Hex.Matrix.sortInjTuple_mem_selectedColumnTuples
open _root_.P2MLLL.t19afdfff renaming h35 → _p2mH35
open _root_.P2MLLL.t19afdfff renaming h36 → Hex.Matrix.sortInjTuple_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h36 → _p2mH36
open _root_.P2MLLL.t19afdfff renaming h37 → Hex.Matrix.sort_reconstruct_get
open _root_.P2MLLL.t19afdfff renaming h37 → _p2mH37
open _root_.P2MLLL.t19afdfff renaming h78 → Hex.Matrix.columnRankNat_injective_of_injective
open _root_.P2MLLL.t19afdfff renaming h78 → _p2mH78
open _root_.P2MLLL.t19afdfff renaming h79 → Hex.Matrix.columnRankNat_inv_apply
open _root_.P2MLLL.t19afdfff renaming h79 → _p2mH79
open _root_.P2MLLL.t19afdfff renaming h80 → Hex.Matrix.columnRankNat_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h80 → _p2mH80
open _root_.P2MLLL.t19afdfff renaming h81 → Hex.Matrix.columnRankNat_strictMono
open _root_.P2MLLL.t19afdfff renaming h81 → _p2mH81
open _root_.P2MLLL.t19afdfff renaming h82 → Hex.Matrix.columnTupleExpansionTerm_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h82 → _p2mH82
open _root_.P2MLLL.t19afdfff renaming h83 → Hex.Matrix.columnTupleExpansion_reconstruct_orbit_sum
open _root_.P2MLLL.t19afdfff renaming h83 → _p2mH83
open _root_.P2MLLL.t19afdfff renaming h84 → Hex.Matrix.columnTupleExpansion_selectedPerm_collapse
open _root_.P2MLLL.t19afdfff renaming h84 → _p2mH84
open _root_.P2MLLL.t19afdfff renaming h85 → Hex.Matrix.columnTupleMatrix_reconstructInjTuple_eq
open _root_.P2MLLL.t19afdfff renaming h85 → _p2mH85
open _root_.P2MLLL.t19afdfff renaming h86 → Hex.Matrix.countP_finRange_val_lt
open _root_.P2MLLL.t19afdfff renaming h86 → _p2mH86
open _root_.P2MLLL.t19afdfff renaming h87 → Hex.Matrix.countP_lt_countP
open _root_.P2MLLL.t19afdfff renaming h87 → _p2mH87
open _root_.P2MLLL.t19afdfff renaming h88 → Hex.Matrix.foldl_filter_zero
open _root_.P2MLLL.t19afdfff renaming h88 → _p2mH88
open _root_.P2MLLL.t19afdfff renaming h89 → Hex.Matrix.foldl_sq_nonneg
open _root_.P2MLLL.t19afdfff renaming h89 → _p2mH89
open _root_.P2MLLL.t19afdfff renaming h90 → Hex.Matrix.foldl_sq_nonneg_start
open _root_.P2MLLL.t19afdfff renaming h90 → _p2mH90
open _root_.P2MLLL.t19afdfff renaming h91 → Hex.Matrix.get_lt_rank
open _root_.P2MLLL.t19afdfff renaming h91 → _p2mH91
open _root_.P2MLLL.t19afdfff renaming h92 → Hex.Matrix.isStrictlyIncreasingColumnTuple_val_lt_iff
open _root_.P2MLLL.t19afdfff renaming h92 → _p2mH92
open _root_.P2MLLL.t19afdfff renaming h93 → Hex.Matrix.mem_selectedColumnTuplesUpTo_imp
open _root_.P2MLLL.t19afdfff renaming h93 → _p2mH93
open _root_.P2MLLL.t19afdfff renaming h94 → Hex.Matrix.mem_selectionsUpTo
open _root_.P2MLLL.t19afdfff renaming h94 → _p2mH94
open _root_.P2MLLL.t19afdfff renaming h95 → Hex.Matrix.permutationVectors_count_val_lt
open _root_.P2MLLL.t19afdfff renaming h95 → _p2mH95
open _root_.P2MLLL.t19afdfff renaming h96 → Hex.Matrix.permutationVectors_getElem_injective
open _root_.P2MLLL.t19afdfff renaming h96 → _p2mH96
open _root_.P2MLLL.t19afdfff renaming h97 → Hex.Matrix.permutationVectors_map_reconstruct_nodup
open _root_.P2MLLL.t19afdfff renaming h97 → _p2mH97
open _root_.P2MLLL.t19afdfff renaming h98 → Hex.Matrix.permutationVectors_toList_perm_finRange
open _root_.P2MLLL.t19afdfff renaming h98 → _p2mH98
open _root_.P2MLLL.t19afdfff renaming h99 → Hex.Matrix.selectedColumnTuplesUpTo_nodup
open _root_.P2MLLL.t19afdfff renaming h99 → _p2mH99
open _root_.P2MLLL.t19afdfff renaming h100 → Hex.Matrix.sortInjPerm_inv_apply
open _root_.P2MLLL.t19afdfff renaming h100 → _p2mH100
open _root_.P2MLLL.t19afdfff renaming h101 → Hex.Matrix.sortInjPerm_toList_nodup
open _root_.P2MLLL.t19afdfff renaming h101 → _p2mH101
open _root_.P2MLLL.t19afdfff renaming h102 → Hex.Matrix.vector_ofFn_getElem_fin
open _root_.P2MLLL.t19afdfff renaming h102 → _p2mH102

end Hex
open _root_.P2MLLL.t19afdfff renaming h0 → Hex.Matrix.columnTupleCoeff_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h0 → _p2mH0
open _root_.P2MLLL.t19afdfff renaming h1 → Hex.Matrix.columnTupleExpansion_refold_selectedPerm
open _root_.P2MLLL.t19afdfff renaming h1 → _p2mH1
open _root_.P2MLLL.t19afdfff renaming h14 → Hex.Matrix.det_gram_sum_sq
open _root_.P2MLLL.t19afdfff renaming h14 → _p2mH14
open _root_.P2MLLL.t19afdfff renaming h21 → Hex.Matrix.getElem_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h21 → _p2mH21
open _root_.P2MLLL.t19afdfff renaming h23 → Hex.Matrix.isStrictlyIncreasingColumnTuple_injective
open _root_.P2MLLL.t19afdfff renaming h23 → _p2mH23
open _root_.P2MLLL.t19afdfff renaming h24 → Hex.Matrix.isStrictlyIncreasingColumnTuple_sortInjTuple
open _root_.P2MLLL.t19afdfff renaming h24 → _p2mH24
open _root_.P2MLLL.t19afdfff renaming h25 → Hex.Matrix.mem_columnTupleVectors
open _root_.P2MLLL.t19afdfff renaming h25 → _p2mH25
open _root_.P2MLLL.t19afdfff renaming h26 → Hex.Matrix.mem_selPerm_reconstructed_iff
open _root_.P2MLLL.t19afdfff renaming h26 → _p2mH26
open _root_.P2MLLL.t19afdfff renaming h27 → Hex.Matrix.mem_selectedColumnTuples_iff
open _root_.P2MLLL.t19afdfff renaming h27 → _p2mH27
open _root_.P2MLLL.t19afdfff renaming h28 → Hex.Matrix.reconstructInjTuple_injective
open _root_.P2MLLL.t19afdfff renaming h28 → _p2mH28
open _root_.P2MLLL.t19afdfff renaming h29 → Hex.Matrix.reconstructInjTuple_sortInj
open _root_.P2MLLL.t19afdfff renaming h29 → _p2mH29
open _root_.P2MLLL.t19afdfff renaming h30 → Hex.Matrix.selPerm_reconstructed_list_nodup
open _root_.P2MLLL.t19afdfff renaming h30 → _p2mH30
open _root_.P2MLLL.t19afdfff renaming h31 → Hex.Matrix.selectedColumnTuples_nodup
open _root_.P2MLLL.t19afdfff renaming h31 → _p2mH31
open _root_.P2MLLL.t19afdfff renaming h32 → Hex.Matrix.sortInjPerm_getElem_val
open _root_.P2MLLL.t19afdfff renaming h32 → _p2mH32
open _root_.P2MLLL.t19afdfff renaming h33 → Hex.Matrix.sortInjPerm_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h33 → _p2mH33
open _root_.P2MLLL.t19afdfff renaming h34 → Hex.Matrix.sortInjPerm_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h34 → _p2mH34
open _root_.P2MLLL.t19afdfff renaming h35 → Hex.Matrix.sortInjTuple_mem_selectedColumnTuples
open _root_.P2MLLL.t19afdfff renaming h35 → _p2mH35
open _root_.P2MLLL.t19afdfff renaming h36 → Hex.Matrix.sortInjTuple_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h36 → _p2mH36
open _root_.P2MLLL.t19afdfff renaming h37 → Hex.Matrix.sort_reconstruct_get
open _root_.P2MLLL.t19afdfff renaming h37 → _p2mH37
open _root_.P2MLLL.t19afdfff renaming h78 → Hex.Matrix.columnRankNat_injective_of_injective
open _root_.P2MLLL.t19afdfff renaming h78 → _p2mH78
open _root_.P2MLLL.t19afdfff renaming h79 → Hex.Matrix.columnRankNat_inv_apply
open _root_.P2MLLL.t19afdfff renaming h79 → _p2mH79
open _root_.P2MLLL.t19afdfff renaming h80 → Hex.Matrix.columnRankNat_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h80 → _p2mH80
open _root_.P2MLLL.t19afdfff renaming h81 → Hex.Matrix.columnRankNat_strictMono
open _root_.P2MLLL.t19afdfff renaming h81 → _p2mH81
open _root_.P2MLLL.t19afdfff renaming h82 → Hex.Matrix.columnTupleExpansionTerm_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h82 → _p2mH82
open _root_.P2MLLL.t19afdfff renaming h83 → Hex.Matrix.columnTupleExpansion_reconstruct_orbit_sum
open _root_.P2MLLL.t19afdfff renaming h83 → _p2mH83
open _root_.P2MLLL.t19afdfff renaming h84 → Hex.Matrix.columnTupleExpansion_selectedPerm_collapse
open _root_.P2MLLL.t19afdfff renaming h84 → _p2mH84
open _root_.P2MLLL.t19afdfff renaming h85 → Hex.Matrix.columnTupleMatrix_reconstructInjTuple_eq
open _root_.P2MLLL.t19afdfff renaming h85 → _p2mH85
open _root_.P2MLLL.t19afdfff renaming h86 → Hex.Matrix.countP_finRange_val_lt
open _root_.P2MLLL.t19afdfff renaming h86 → _p2mH86
open _root_.P2MLLL.t19afdfff renaming h87 → Hex.Matrix.countP_lt_countP
open _root_.P2MLLL.t19afdfff renaming h87 → _p2mH87
open _root_.P2MLLL.t19afdfff renaming h88 → Hex.Matrix.foldl_filter_zero
open _root_.P2MLLL.t19afdfff renaming h88 → _p2mH88
open _root_.P2MLLL.t19afdfff renaming h89 → Hex.Matrix.foldl_sq_nonneg
open _root_.P2MLLL.t19afdfff renaming h89 → _p2mH89
open _root_.P2MLLL.t19afdfff renaming h90 → Hex.Matrix.foldl_sq_nonneg_start
open _root_.P2MLLL.t19afdfff renaming h90 → _p2mH90
open _root_.P2MLLL.t19afdfff renaming h91 → Hex.Matrix.get_lt_rank
open _root_.P2MLLL.t19afdfff renaming h91 → _p2mH91
open _root_.P2MLLL.t19afdfff renaming h92 → Hex.Matrix.isStrictlyIncreasingColumnTuple_val_lt_iff
open _root_.P2MLLL.t19afdfff renaming h92 → _p2mH92
open _root_.P2MLLL.t19afdfff renaming h93 → Hex.Matrix.mem_selectedColumnTuplesUpTo_imp
open _root_.P2MLLL.t19afdfff renaming h93 → _p2mH93
open _root_.P2MLLL.t19afdfff renaming h94 → Hex.Matrix.mem_selectionsUpTo
open _root_.P2MLLL.t19afdfff renaming h94 → _p2mH94
open _root_.P2MLLL.t19afdfff renaming h95 → Hex.Matrix.permutationVectors_count_val_lt
open _root_.P2MLLL.t19afdfff renaming h95 → _p2mH95
open _root_.P2MLLL.t19afdfff renaming h96 → Hex.Matrix.permutationVectors_getElem_injective
open _root_.P2MLLL.t19afdfff renaming h96 → _p2mH96
open _root_.P2MLLL.t19afdfff renaming h97 → Hex.Matrix.permutationVectors_map_reconstruct_nodup
open _root_.P2MLLL.t19afdfff renaming h97 → _p2mH97
open _root_.P2MLLL.t19afdfff renaming h98 → Hex.Matrix.permutationVectors_toList_perm_finRange
open _root_.P2MLLL.t19afdfff renaming h98 → _p2mH98
open _root_.P2MLLL.t19afdfff renaming h99 → Hex.Matrix.selectedColumnTuplesUpTo_nodup
open _root_.P2MLLL.t19afdfff renaming h99 → _p2mH99
open _root_.P2MLLL.t19afdfff renaming h100 → Hex.Matrix.sortInjPerm_inv_apply
open _root_.P2MLLL.t19afdfff renaming h100 → _p2mH100
open _root_.P2MLLL.t19afdfff renaming h101 → Hex.Matrix.sortInjPerm_toList_nodup
open _root_.P2MLLL.t19afdfff renaming h101 → _p2mH101
open _root_.P2MLLL.t19afdfff renaming h102 → Hex.Matrix.vector_ofFn_getElem_fin
open _root_.P2MLLL.t19afdfff renaming h102 → _p2mH102


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t19afdfff renaming h0 → Hex.Matrix.columnTupleCoeff_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h0 → _p2mH0
open _root_.P2MLLL.t19afdfff renaming h1 → Hex.Matrix.columnTupleExpansion_refold_selectedPerm
open _root_.P2MLLL.t19afdfff renaming h1 → _p2mH1
open _root_.P2MLLL.t19afdfff renaming h14 → Hex.Matrix.det_gram_sum_sq
open _root_.P2MLLL.t19afdfff renaming h14 → _p2mH14
open _root_.P2MLLL.t19afdfff renaming h21 → Hex.Matrix.getElem_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h21 → _p2mH21
open _root_.P2MLLL.t19afdfff renaming h23 → Hex.Matrix.isStrictlyIncreasingColumnTuple_injective
open _root_.P2MLLL.t19afdfff renaming h23 → _p2mH23
open _root_.P2MLLL.t19afdfff renaming h24 → Hex.Matrix.isStrictlyIncreasingColumnTuple_sortInjTuple
open _root_.P2MLLL.t19afdfff renaming h24 → _p2mH24
open _root_.P2MLLL.t19afdfff renaming h25 → Hex.Matrix.mem_columnTupleVectors
open _root_.P2MLLL.t19afdfff renaming h25 → _p2mH25
open _root_.P2MLLL.t19afdfff renaming h26 → Hex.Matrix.mem_selPerm_reconstructed_iff
open _root_.P2MLLL.t19afdfff renaming h26 → _p2mH26
open _root_.P2MLLL.t19afdfff renaming h27 → Hex.Matrix.mem_selectedColumnTuples_iff
open _root_.P2MLLL.t19afdfff renaming h27 → _p2mH27
open _root_.P2MLLL.t19afdfff renaming h28 → Hex.Matrix.reconstructInjTuple_injective
open _root_.P2MLLL.t19afdfff renaming h28 → _p2mH28
open _root_.P2MLLL.t19afdfff renaming h29 → Hex.Matrix.reconstructInjTuple_sortInj
open _root_.P2MLLL.t19afdfff renaming h29 → _p2mH29
open _root_.P2MLLL.t19afdfff renaming h30 → Hex.Matrix.selPerm_reconstructed_list_nodup
open _root_.P2MLLL.t19afdfff renaming h30 → _p2mH30
open _root_.P2MLLL.t19afdfff renaming h31 → Hex.Matrix.selectedColumnTuples_nodup
open _root_.P2MLLL.t19afdfff renaming h31 → _p2mH31
open _root_.P2MLLL.t19afdfff renaming h32 → Hex.Matrix.sortInjPerm_getElem_val
open _root_.P2MLLL.t19afdfff renaming h32 → _p2mH32
open _root_.P2MLLL.t19afdfff renaming h33 → Hex.Matrix.sortInjPerm_mem_permutationVectors
open _root_.P2MLLL.t19afdfff renaming h33 → _p2mH33
open _root_.P2MLLL.t19afdfff renaming h34 → Hex.Matrix.sortInjPerm_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h34 → _p2mH34
open _root_.P2MLLL.t19afdfff renaming h35 → Hex.Matrix.sortInjTuple_mem_selectedColumnTuples
open _root_.P2MLLL.t19afdfff renaming h35 → _p2mH35
open _root_.P2MLLL.t19afdfff renaming h36 → Hex.Matrix.sortInjTuple_reconstructInjTuple
open _root_.P2MLLL.t19afdfff renaming h36 → _p2mH36
open _root_.P2MLLL.t19afdfff renaming h37 → Hex.Matrix.sort_reconstruct_get
open _root_.P2MLLL.t19afdfff renaming h37 → _p2mH37


set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.Hex.Matrix.__p2m_proof_19afdfff033044c5b8d3) := @_root_.Hex.Matrix.__p2m_proof_19afdfff033044c5b8d3
