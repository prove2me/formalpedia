-- Prove2me | solution 1 for Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T04:32:13.307616+00:00
-- url     : https://prove2.me/submissions/c1b901ac-8f35-4256-8b9a-c475ef6debd4

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



import Definitions.Def_LARLLL_BareissProgram
import Definitions.Def_LARLLL_Foundation01
import Definitions.Def_LARLLL_IntegerGramSchmidt
import Init
import Init.Data.List.Sort.Basic
import Init.Grind.Ring.Field
import Std
import Std.Data.ExtTreeMap.Lemmas

namespace P2MLLL.t00ef6f00
end P2MLLL.t00ef6f00
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
theorem _root_.P2MLLL.t00ef6f00.h10 (xs : List α) (f : α → R) (z : R) :
    xs.foldl (fun acc x => acc + f x) z
      = z + xs.foldl (fun acc x => acc + f x) 0 :=
  calc xs.foldl (fun acc x => acc + f x) z
      = (xs.map f).foldl (· + ·) z :=
        (List.foldl_map (l := xs) (f := f) (g := (· + ·)) (init := z)).symm
    _ = (xs.map f).foldl (· + ·) (z + 0) := by rw [Lean.Grind.Semiring.add_zero]
    _ = z + (xs.map f).foldl (· + ·) 0 := List.foldl_assoc
    _ = z + xs.foldl (fun acc x => acc + f x) 0 := by
        rw [List.foldl_map (l := xs) (f := f) (g := (· + ·)) (init := 0)]
open _root_.P2MLLL.t00ef6f00 renaming h10 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t00ef6f00 renaming h10 → _p2mH10


/-! # All-zero collapse -/



set_option maxRecDepth 8192
/-- An additive fold-sum whose body adds a literal `0` returns the initial
accumulator. -/
theorem _root_.P2MLLL.t00ef6f00.h11 (xs : List α) (z : R) :
    xs.foldl (fun acc _ => acc + 0) z = z :=
  foldl_add_eq_self xs (fun _ => 0) z fun _ _ => rfl
open _root_.P2MLLL.t00ef6f00 renaming h11 → List.foldl_add_zero
open _root_.P2MLLL.t00ef6f00 renaming h11 → _p2mH11


/-! # Scalar factoring -/







end Semiring
open _root_.P2MLLL.t00ef6f00 renaming h10 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t00ef6f00 renaming h10 → _p2mH10
open _root_.P2MLLL.t00ef6f00 renaming h11 → List.foldl_add_zero
open _root_.P2MLLL.t00ef6f00 renaming h11 → _p2mH11


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
theorem _root_.P2MLLL.t00ef6f00.h9 {γ : Type w} (xs : List α) (ys : List γ) (f : α → γ → R) :
    xs.foldl (fun acc x => acc + ys.foldl (fun acc' y => acc' + f x y) 0) 0 =
      ys.foldl (fun acc y => acc + xs.foldl (fun acc' x => acc' + f x y) 0) 0 := by
  induction xs with
  | nil =>
    simp only [List.foldl_nil]
    exact (_root_.P2MLLL.t00ef6f00.h11 ys 0).symm
  | cons x xs ih =>
    have hLHS :
        (x :: xs).foldl
            (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 =
          ys.foldl (fun acc' y => acc' + f x y) 0 +
            xs.foldl
              (fun acc x' => acc + ys.foldl (fun acc' y => acc' + f x' y) 0) 0 := by
      simp only [List.foldl_cons]
      rw [_root_.P2MLLL.t00ef6f00.h10 xs
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
        rw [_root_.P2MLLL.t00ef6f00.h10 xs (fun x' => f x' y) (0 + f x y)]
        grind
      rw [hfun]
      exact foldl_add_add ys (fun y => f x y)
        (fun y => xs.foldl (fun acc' x' => acc' + f x' y) 0)
    rw [hLHS, hRHS, ih]
open _root_.P2MLLL.t00ef6f00 renaming h9 → List.foldl_add_comm
open _root_.P2MLLL.t00ef6f00 renaming h9 → _p2mH9


end Semiring
open _root_.P2MLLL.t00ef6f00 renaming h9 → List.foldl_add_comm
open _root_.P2MLLL.t00ef6f00 renaming h9 → _p2mH9


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
open _root_.P2MLLL.t00ef6f00 renaming h9 → List.foldl_add_comm
open _root_.P2MLLL.t00ef6f00 renaming h9 → _p2mH9
open _root_.P2MLLL.t00ef6f00 renaming h10 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t00ef6f00 renaming h10 → _p2mH10
open _root_.P2MLLL.t00ef6f00 renaming h11 → List.foldl_add_zero
open _root_.P2MLLL.t00ef6f00 renaming h11 → _p2mH11


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t00ef6f00 renaming h9 → List.foldl_add_comm
open _root_.P2MLLL.t00ef6f00 renaming h9 → _p2mH9
open _root_.P2MLLL.t00ef6f00 renaming h10 → List.foldl_add_eq_add_foldl
open _root_.P2MLLL.t00ef6f00 renaming h10 → _p2mH10
open _root_.P2MLLL.t00ef6f00 renaming h11 → List.foldl_add_zero
open _root_.P2MLLL.t00ef6f00 renaming h11 → _p2mH11

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section





set_option autoImplicit true



section

/-!
Executable Bareiss determinant algorithm for `hex-matrix`.

This module implements fraction-free Bareiss elimination over `Int` in two
layers: a no-pivot recurrence that follows the standard exact-division update,
and a public row-pivoting wrapper that swaps in a nonzero pivot when needed and
tracks the resulting determinant sign. The Mathlib-free layer exposes the
executable data and state needed by later bridge proofs; it does not expose a
theorem identifying the executable Bareiss determinant with the generic
Leibniz determinant.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n : Nat}



namespace BareissData













end BareissData











































set_option maxRecDepth 8192
/-- `stepMatrixWith` preserves diagonal entries whose index is at or before the
current pivot step. -/
@[grind =]
theorem _root_.P2MLLL.t00ef6f00.h6
    [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) (i : Fin n)
    (hi : i.val ≤ k) :
    (stepMatrixWith quot M k pivot prevPivot)[i][i] = M[i][i] := by
  apply stepMatrixWith_eq_of_not_update
  · intro htrail
    exact Nat.not_lt_of_ge hi htrail.1
  · intro hcol
    exact Nat.not_lt_of_ge hi hcol.1
open _root_.P2MLLL.t00ef6f00 renaming h6 → Hex.Matrix.stepMatrixWith_diag_of_le
open _root_.P2MLLL.t00ef6f00 renaming h6 → _p2mH6












































section GenericBareiss

variable [Zero R] [One R] [Neg R] [Sub R] [Mul R] [DecidableEq R]
variable {quot : R → R → R}



































set_option maxRecDepth 8192
omit [One R] [Neg R] in
/-- Diagonal entries at or before the current step are unchanged by subsequent
no-pivot loop iterations. -/
@[grind =]
theorem _root_.P2MLLL.t00ef6f00.h4 (fuel : Nat) (state : BareissState R n)
    (i : Fin n) (hi : i.val ≤ state.step) :
    (noPivotLoopWith quot fuel state).matrix[i][i] = state.matrix[i][i] :=
  noPivotLoopWith_matrix_entry_of_row_le_or_col_lt (quot := quot) fuel state i i (Or.inl hi)
open _root_.P2MLLL.t00ef6f00 renaming h4 → Hex.Matrix.noPivotLoopWith_diag_of_le_step
open _root_.P2MLLL.t00ef6f00 renaming h4 → _p2mH4
































end GenericBareiss
open _root_.P2MLLL.t00ef6f00 renaming h4 → Hex.Matrix.noPivotLoopWith_diag_of_le_step
open _root_.P2MLLL.t00ef6f00 renaming h4 → _p2mH4


















/-! Integer proof-interface compatibility.  These theorems state their
conclusions through the traditional entry points while delegating every proof
to the generic `With` theorem. -/

set_option maxRecDepth 8192
theorem _root_.P2MLLL.t00ef6f00.h8 (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) :
    stepMatrix M k pivot prevPivot =
      Matrix.ofFn fun i j =>
        if hkij : k < i.val ∧ k < j.val then
          let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
          let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
          exactDiv (pivot * M[(i, j)] - M[(i, colK)] * M[(rowK, j)]) prevPivot
        else if k < i.val ∧ j.val = k then
          0
        else
          M[(i, j)] :=
  stepMatrixWith_eq_ofFn exactDiv M k pivot prevPivot
open _root_.P2MLLL.t00ef6f00 renaming h8 → Hex.Matrix.stepMatrix_eq_ofFn
open _root_.P2MLLL.t00ef6f00 renaming h8 → _p2mH8




set_option maxRecDepth 8192
@[grind =]
theorem _root_.P2MLLL.t00ef6f00.h7 (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) (i : Fin n) (hi : i.val ≤ k) :
    (stepMatrix M k pivot prevPivot)[i][i] = M[i][i] :=
  _root_.P2MLLL.t00ef6f00.h6 exactDiv M k pivot prevPivot i hi
open _root_.P2MLLL.t00ef6f00 renaming h7 → Hex.Matrix.stepMatrix_diag_of_le
open _root_.P2MLLL.t00ef6f00 renaming h7 → _p2mH7




























set_option maxRecDepth 8192
@[grind =]
theorem _root_.P2MLLL.t00ef6f00.h5 (fuel : Nat) (state : BareissState Int n)
    (i : Fin n) (hi : i.val ≤ state.step) :
    (noPivotLoop fuel state).matrix[i][i] = state.matrix[i][i] :=
  _root_.P2MLLL.t00ef6f00.h4 (quot := exactDiv) fuel state i hi
open _root_.P2MLLL.t00ef6f00 renaming h5 → Hex.Matrix.noPivotLoop_diag_of_le_step
open _root_.P2MLLL.t00ef6f00 renaming h5 → _p2mH5






















end Matrix
open _root_.P2MLLL.t00ef6f00 renaming h4 → Hex.Matrix.noPivotLoopWith_diag_of_le_step
open _root_.P2MLLL.t00ef6f00 renaming h4 → _p2mH4
open _root_.P2MLLL.t00ef6f00 renaming h5 → Hex.Matrix.noPivotLoop_diag_of_le_step
open _root_.P2MLLL.t00ef6f00 renaming h5 → _p2mH5
open _root_.P2MLLL.t00ef6f00 renaming h6 → Hex.Matrix.stepMatrixWith_diag_of_le
open _root_.P2MLLL.t00ef6f00 renaming h6 → _p2mH6
open _root_.P2MLLL.t00ef6f00 renaming h7 → Hex.Matrix.stepMatrix_diag_of_le
open _root_.P2MLLL.t00ef6f00 renaming h7 → _p2mH7
open _root_.P2MLLL.t00ef6f00 renaming h8 → Hex.Matrix.stepMatrix_eq_ofFn
open _root_.P2MLLL.t00ef6f00 renaming h8 → _p2mH8

end Hex
open _root_.P2MLLL.t00ef6f00 renaming h4 → Hex.Matrix.noPivotLoopWith_diag_of_le_step
open _root_.P2MLLL.t00ef6f00 renaming h4 → _p2mH4
open _root_.P2MLLL.t00ef6f00 renaming h5 → Hex.Matrix.noPivotLoop_diag_of_le_step
open _root_.P2MLLL.t00ef6f00 renaming h5 → _p2mH5
open _root_.P2MLLL.t00ef6f00 renaming h6 → Hex.Matrix.stepMatrixWith_diag_of_le
open _root_.P2MLLL.t00ef6f00 renaming h6 → _p2mH6
open _root_.P2MLLL.t00ef6f00 renaming h7 → Hex.Matrix.stepMatrix_diag_of_le
open _root_.P2MLLL.t00ef6f00 renaming h7 → _p2mH7
open _root_.P2MLLL.t00ef6f00 renaming h8 → Hex.Matrix.stepMatrix_eq_ofFn
open _root_.P2MLLL.t00ef6f00 renaming h8 → _p2mH8


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t00ef6f00 renaming h4 → Hex.Matrix.noPivotLoopWith_diag_of_le_step
open _root_.P2MLLL.t00ef6f00 renaming h4 → _p2mH4
open _root_.P2MLLL.t00ef6f00 renaming h5 → Hex.Matrix.noPivotLoop_diag_of_le_step
open _root_.P2MLLL.t00ef6f00 renaming h5 → _p2mH5
open _root_.P2MLLL.t00ef6f00 renaming h6 → Hex.Matrix.stepMatrixWith_diag_of_le
open _root_.P2MLLL.t00ef6f00 renaming h6 → _p2mH6
open _root_.P2MLLL.t00ef6f00 renaming h7 → Hex.Matrix.stepMatrix_diag_of_le
open _root_.P2MLLL.t00ef6f00 renaming h7 → _p2mH7
open _root_.P2MLLL.t00ef6f00 renaming h8 → Hex.Matrix.stepMatrix_eq_ofFn
open _root_.P2MLLL.t00ef6f00 renaming h8 → _p2mH8

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section




set_option autoImplicit true



section

/-!
Executable array/loop machinery for the integer scaled Gram-Schmidt pass in
`hex-gram-schmidt`.

This module defines the integer-determinant surface (`gramDet` and
`independent`, the leading Gram matrices (`leadingGramMatrixInt`/`Rat`),
`scaledCoeffMatrix`, lattice membership `memLattice`, and the no-pivot Bareiss
determinant reader `gramDetVecEntry`) together with the mutable row-major array
kernel that computes the scaled coefficients fraction-free. The kernel includes the
nested-array storage (`gramRows`, `zeroRows`, `getArrayEntry`/`setArrayEntry`,
`rowsToMatrix`), the Bareiss-style elimination sweep `stepScaledRows` and
column-writer `writeScaledColumn`, the driver `scaledCoeffArrayLoop`, the two
formulations `scaledCoeffRows` (reference) and `scaledCoeffRowsSchur` (live
per-row Schur recurrence, with `schurSigma`/`schurScaledCoeffEntry`), and a
large body of frame/size bookkeeping lemmas plus the per-step correspondence
`rowsToMatrix_stepScaledRows_eq` between the array update and `Matrix.stepMatrix`.
-/
namespace Hex

namespace GramSchmidt











end GramSchmidt

namespace GramSchmidt.Int































set_option maxRecDepth 8192
/-- Reading entry `(i, j)` of `gramRows b` recovers the Gram matrix entry
`(gramMatrix b)[i][j]`. -/
 theorem _root_.P2MLLL.t00ef6f00.h34 (b : Matrix Int n m) (i j : Fin n) :
    getArrayEntry (gramRows b) i.val j.val = (Matrix.gramMatrix b)[i][j] := by
  rw [Matrix.getElem_gramMatrix]
  simp [getArrayEntry, gramRows, Vector.dotProduct]
open _root_.P2MLLL.t00ef6f00 renaming h34 → Hex.GramSchmidt.Int.getArrayEntry_gramRows
open _root_.P2MLLL.t00ef6f00 renaming h34 → _p2mH34




set_option maxRecDepth 8192
/-- `rowsToMatrix` inverts `gramRows`, recovering `gramMatrix b` from its
nested-array packaging. -/
 theorem _root_.P2MLLL.t00ef6f00.h69 (b : Matrix Int n m) :
    rowsToMatrix (gramRows b) n = Matrix.gramMatrix b := by
  apply Hex.Matrix.ext_getElem
  intro i j
  rw [rowsToMatrix, Matrix.getElem_ofFn, _root_.P2MLLL.t00ef6f00.h34]
open _root_.P2MLLL.t00ef6f00 renaming h69 → Hex.GramSchmidt.Int.rowsToMatrix_gramRows
open _root_.P2MLLL.t00ef6f00 renaming h69 → _p2mH69




set_option maxRecDepth 8192
/-- Reading back the just-written index of `Array.set!` returns the written
value, when the index is in bounds. -/
 theorem _root_.P2MLLL.t00ef6f00.h25 {α : Type} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.set! i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  simp [Array.getD, Array.set!_eq_setIfInBounds, hi]
open _root_.P2MLLL.t00ef6f00 renaming h25 → Hex.GramSchmidt.Int.array_getElem!_set!_same
open _root_.P2MLLL.t00ef6f00 renaming h25 → _p2mH25


set_option maxRecDepth 8192
/-- Reading a different index after `Array.set!` returns the original element. -/
 theorem _root_.P2MLLL.t00ef6f00.h24 {α : Type} [Inhabited α]
    (xs : Array α) {i j : Nat} (hij : j ≠ i) (v : α) :
    (xs.set! i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.set!
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hij.symm]
  · simp [hi]
open _root_.P2MLLL.t00ef6f00 renaming h24 → Hex.GramSchmidt.Int.array_getElem!_set!_ne
open _root_.P2MLLL.t00ef6f00 renaming h24 → _p2mH24


set_option maxRecDepth 8192
/-- `setArrayEntry` leaves entries in any other row unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h47
    (rows : Array (Array Int)) (row col r c : Nat) (value : Int) (hr : r ≠ row) :
    getArrayEntry (setArrayEntry rows row col value) r c = getArrayEntry rows r c := by
  grind [getArrayEntry, setArrayEntry]
open _root_.P2MLLL.t00ef6f00 renaming h47 → Hex.GramSchmidt.Int.getArrayEntry_setArrayEntry_of_row_ne
open _root_.P2MLLL.t00ef6f00 renaming h47 → _p2mH47


set_option maxRecDepth 8192
/-- `setArrayEntry` leaves entries in any other column of the written row
unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h46
    (rows : Array (Array Int)) (row col c : Nat) (value : Int) (hc : c ≠ col) :
    getArrayEntry (setArrayEntry rows row col value) row c = getArrayEntry rows row c := by
  grind [getArrayEntry, setArrayEntry]
open _root_.P2MLLL.t00ef6f00 renaming h46 → Hex.GramSchmidt.Int.getArrayEntry_setArrayEntry_of_col_ne
open _root_.P2MLLL.t00ef6f00 renaming h46 → _p2mH46


set_option maxRecDepth 8192
/-- Reading back the just-written entry of `setArrayEntry` returns the written
value, when both indices are in bounds. -/
 theorem _root_.P2MLLL.t00ef6f00.h48
    (rows : Array (Array Int)) (row col : Nat) (value : Int)
    (hrow : row < rows.size) (hcol : col < rows[row]!.size) :
    getArrayEntry (setArrayEntry rows row col value) row col = value := by
  unfold getArrayEntry setArrayEntry
  rw [_root_.P2MLLL.t00ef6f00.h25 rows hrow (rows[row]!.set! col value)]
  exact _root_.P2MLLL.t00ef6f00.h25 rows[row]! hcol value
open _root_.P2MLLL.t00ef6f00 renaming h48 → Hex.GramSchmidt.Int.getArrayEntry_setArrayEntry_self
open _root_.P2MLLL.t00ef6f00 renaming h48 → _p2mH48


set_option maxRecDepth 8192
/-- `setArrayEntry` preserves the outer-array size. -/
 theorem _root_.P2MLLL.t00ef6f00.h77 (rows : Array (Array Int)) (row col : Nat) (value : Int) :
    (setArrayEntry rows row col value).size = rows.size := by
  simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
open _root_.P2MLLL.t00ef6f00 renaming h77 → Hex.GramSchmidt.Int.setArrayEntry_size
open _root_.P2MLLL.t00ef6f00 renaming h77 → _p2mH77


set_option maxRecDepth 8192
/-- `setArrayEntry` preserves each inner row's size. -/
 theorem _root_.P2MLLL.t00ef6f00.h76
    (rows : Array (Array Int)) (row col r : Nat) (value : Int) :
    (setArrayEntry rows row col value)[r]!.size = rows[r]!.size := by
  unfold setArrayEntry
  by_cases hrow : r = row
  · subst r
    by_cases hbound : row < rows.size
    · rw [_root_.P2MLLL.t00ef6f00.h25 _ hbound]
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    · simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hbound]
  · simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.set!_eq_setIfInBounds]
    have hne : row ≠ r := fun h => hrow h.symm
    by_cases hbound : row < rows.size
    · simp [hne]
    · simp [Array.setIfInBounds, hbound]
open _root_.P2MLLL.t00ef6f00 renaming h76 → Hex.GramSchmidt.Int.setArrayEntry_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h76 → _p2mH76


set_option maxRecDepth 8192
/-- A `foldl` of column-`k` writes over rows all exceeding `k` leaves entries
strictly above the diagonal (`i < j`) unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h29
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k i j : Nat)
    (hxs : ∀ x ∈ xs, k < x) (hij : i < j) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        i j =
      getArrayEntry coeffs i j := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : k < x := hxs x (by simp)
      have hxs' : ∀ y ∈ xs, k < y := by
        intro y hy
        exact hxs y (by simp [hy])
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hxs']
      by_cases hrow : i = x
      · subst x
        rw [_root_.P2MLLL.t00ef6f00.h46]
        omega
      · rw [_root_.P2MLLL.t00ef6f00.h47]
        exact hrow
open _root_.P2MLLL.t00ef6f00 renaming h29 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_col_above
open _root_.P2MLLL.t00ef6f00 renaming h29 → _p2mH29


set_option maxRecDepth 8192
/-- A `foldl` of column-`k` writes over rows all exceeding `k` leaves entries
in rows at or below `k` unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h32
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k i j : Nat)
    (hxs : ∀ x ∈ xs, k < x) (hi : i ≤ k) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        i j =
      getArrayEntry coeffs i j := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : k < x := hxs x (by simp)
      have hxs' : ∀ y ∈ xs, k < y := by
        intro y hy
        exact hxs y (by simp [hy])
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hxs',
        _root_.P2MLLL.t00ef6f00.h47]
      omega
open _root_.P2MLLL.t00ef6f00 renaming h32 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_row_ne
open _root_.P2MLLL.t00ef6f00 renaming h32 → _p2mH32


set_option maxRecDepth 8192
/-- A column-targeted `foldl` preserves rows whose index is absent from the
write list. -/
 theorem _root_.P2MLLL.t00ef6f00.h33
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r c : Nat)
    (hr : r ∉ xs) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r c =
      getArrayEntry coeffs r c := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hrx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hrxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hrxs,
        _root_.P2MLLL.t00ef6f00.h47]
      exact hrx
open _root_.P2MLLL.t00ef6f00 renaming h33 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_row_notMem
open _root_.P2MLLL.t00ef6f00 renaming h33 → _p2mH33


set_option maxRecDepth 8192
/-- A column-targeted `foldl` of `setArrayEntry`s at column `k` leaves entries
in any other column unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h31
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r c : Nat) (hc : c ≠ k) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r c =
      getArrayEntry coeffs r c := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k))]
      by_cases hrow : r = x
      · subst x
        rw [_root_.P2MLLL.t00ef6f00.h46 _ _ _ _ _ hc]
      · rw [_root_.P2MLLL.t00ef6f00.h47]
        exact hrow
open _root_.P2MLLL.t00ef6f00 renaming h31 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_col_ne
open _root_.P2MLLL.t00ef6f00 renaming h31 → _p2mH31


set_option maxRecDepth 8192
/-- A column-targeted `foldl` records the source-row value at an updated row.
The row list is nodup, so the final write to `r` is the unique write to that
row. -/
 theorem _root_.P2MLLL.t00ef6f00.h30
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r : Nat)
    (hrmem : r ∈ xs) (hnodup : xs.Nodup)
    (hrow : r < coeffs.size) (hcol : k < coeffs[r]!.size) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r k =
      getArrayEntry rows r k := by
  induction xs generalizing coeffs with
  | nil =>
      exact absurd hrmem (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hrmem with hr_eq | hr_in
      · subst x
        rw [_root_.P2MLLL.t00ef6f00.h33]
        · exact _root_.P2MLLL.t00ef6f00.h48 coeffs r k
            (getArrayEntry rows r k) hrow hcol
        · exact hxnotmem
      · have hr_ne_x : r ≠ x := by
          intro h
          subst r
          exact hxnotmem hr_in
        have hrow' : r < (setArrayEntry coeffs x k (getArrayEntry rows x k)).size := by
          simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hrow]
        have hcol' :
            k < (setArrayEntry coeffs x k (getArrayEntry rows x k))[r]!.size := by
          unfold setArrayEntry
          rw [_root_.P2MLLL.t00ef6f00.h24 _ hr_ne_x]
          exact hcol
        exact ih (setArrayEntry coeffs x k (getArrayEntry rows x k))
          hr_in hnodup' hrow' hcol'
open _root_.P2MLLL.t00ef6f00 renaming h30 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_col_mem
open _root_.P2MLLL.t00ef6f00 renaming h30 → _p2mH30


set_option maxRecDepth 8192
/-- A `foldl` whose write value reads the same column being written still
leaves non-member indices unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h62
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∉ xs) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr)[r]! = arr[r]! := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      have hx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih _ hxs]
      grind
open _root_.P2MLLL.t00ef6f00 renaming h62 → Hex.GramSchmidt.Int.getElem!_foldl_setSelf_of_notMem
open _root_.P2MLLL.t00ef6f00 renaming h62 → _p2mH62


set_option maxRecDepth 8192
/-- A `foldl` whose write value reads the same column being written writes the
function of the original value at every member index of a `Nodup` list. -/
 theorem _root_.P2MLLL.t00ef6f00.h61
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∈ xs) (hnodup : xs.Nodup) (hbound : r < arr.size) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr)[r]! = f r arr[r]! := by
  induction xs generalizing arr with
  | nil => exact absurd hr (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hr with hr_eq | hr_in
      · subst hr_eq
        rw [_root_.P2MLLL.t00ef6f00.h62 _ _ _ _ hxnotmem]
        grind
      · have hr_ne_x : r ≠ x := by
          intro h
          exact hxnotmem (h ▸ hr_in)
        have hbound' : r < (arr.set! x (f x arr[x]!)).size := by
          simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hbound]
        rw [ih _ hr_in hnodup' hbound']
        grind
open _root_.P2MLLL.t00ef6f00 renaming h61 → Hex.GramSchmidt.Int.getElem!_foldl_setSelf_of_mem_nodup
open _root_.P2MLLL.t00ef6f00 renaming h61 → _p2mH61


set_option maxRecDepth 8192
/-- A `foldl` that sets indices via values read from the row itself preserves
the array size. -/
 theorem _root_.P2MLLL.t00ef6f00.h79
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
open _root_.P2MLLL.t00ef6f00 renaming h79 → Hex.GramSchmidt.Int.size_foldl_setSelf
open _root_.P2MLLL.t00ef6f00 renaming h79 → _p2mH79


set_option maxRecDepth 8192
/-- `Array.modify` equals `Array.set!` applied to the function's value at the
current entry. -/
 theorem _root_.P2MLLL.t00ef6f00.h67
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α) :
    arr.modify i f = arr.set! i (f arr[i]!) := by
  -- `Array.modify`/`modifyM` are public but not `@[expose]`d, so prove via the
  -- exposed `@[grind]` lemma API rather than unfolding the definitions.
  grind
open _root_.P2MLLL.t00ef6f00 renaming h67 → Hex.GramSchmidt.Int.modify_eq_set!
open _root_.P2MLLL.t00ef6f00 renaming h67 → _p2mH67


set_option maxRecDepth 8192
/-- `Array.modify` leaves any index other than the modified one unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h63
    {α : Type} [Inhabited α] (arr : Array α) (i r : Nat) (f : α → α)
    (hr : r ≠ i) :
    (arr.modify i f)[r]! = arr[r]! := by
  rw [_root_.P2MLLL.t00ef6f00.h67]
  grind
open _root_.P2MLLL.t00ef6f00 renaming h63 → Hex.GramSchmidt.Int.getElem!_modify_ne
open _root_.P2MLLL.t00ef6f00 renaming h63 → _p2mH63


set_option maxRecDepth 8192
/-- Reading back the modified index of `Array.modify` returns `f` applied to the
original entry, when the index is in bounds. -/
 theorem _root_.P2MLLL.t00ef6f00.h64
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α)
    (hi : i < arr.size) :
    (arr.modify i f)[i]! = f arr[i]! := by
  rw [_root_.P2MLLL.t00ef6f00.h67]
  grind
open _root_.P2MLLL.t00ef6f00 renaming h64 → Hex.GramSchmidt.Int.getElem!_modify_self
open _root_.P2MLLL.t00ef6f00 renaming h64 → _p2mH64


set_option maxRecDepth 8192
/-- `Array.modify` preserves the array size. -/
 theorem _root_.P2MLLL.t00ef6f00.h68
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α) :
    (arr.modify i f).size = arr.size := by
  rw [_root_.P2MLLL.t00ef6f00.h67]
  simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
open _root_.P2MLLL.t00ef6f00 renaming h68 → Hex.GramSchmidt.Int.modify_size
open _root_.P2MLLL.t00ef6f00 renaming h68 → _p2mH68


set_option maxRecDepth 8192
/-- A `foldl` that modifies indices appearing in `xs` leaves untouched
indices unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h60
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∉ xs) :
    (xs.foldl (fun next x => next.modify x (f x)) arr)[r]! = arr[r]! := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      have hx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih _ hxs]
      exact _root_.P2MLLL.t00ef6f00.h63 arr x r (f x) hx
open _root_.P2MLLL.t00ef6f00 renaming h60 → Hex.GramSchmidt.Int.getElem!_foldl_modify_of_notMem
open _root_.P2MLLL.t00ef6f00 renaming h60 → _p2mH60


set_option maxRecDepth 8192
/-- A `foldl` that modifies indices appearing in a `Nodup` list `xs` writes
the modified original value at every member index `r` that is in-bounds for the
input array. -/
 theorem _root_.P2MLLL.t00ef6f00.h59
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∈ xs) (hnodup : xs.Nodup) (hbound : r < arr.size) :
    (xs.foldl (fun next x => next.modify x (f x)) arr)[r]! = f r arr[r]! := by
  induction xs generalizing arr with
  | nil => exact absurd hr (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hr with hr_eq | hr_in
      · subst hr_eq
        rw [_root_.P2MLLL.t00ef6f00.h60 _ _ _ _ hxnotmem]
        exact _root_.P2MLLL.t00ef6f00.h64 arr r (f r) hbound
      · have hr_ne_x : r ≠ x := by
          intro h
          exact hxnotmem (h ▸ hr_in)
        have hbound' : r < (arr.modify x (f x)).size := by
          rw [_root_.P2MLLL.t00ef6f00.h68]
          exact hbound
        rw [ih _ hr_in hnodup' hbound', _root_.P2MLLL.t00ef6f00.h63 arr x r (f x) hr_ne_x]
open _root_.P2MLLL.t00ef6f00 renaming h59 → Hex.GramSchmidt.Int.getElem!_foldl_modify_of_mem_nodup
open _root_.P2MLLL.t00ef6f00 renaming h59 → _p2mH59


set_option maxRecDepth 8192
/-- A `foldl` that modifies indices via `Array.modify` preserves the outer
array size. -/
 theorem _root_.P2MLLL.t00ef6f00.h78
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) :
    (xs.foldl (fun next x => next.modify x (f x)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact _root_.P2MLLL.t00ef6f00.h68 arr x (f x)
open _root_.P2MLLL.t00ef6f00 renaming h78 → Hex.GramSchmidt.Int.size_foldl_modify
open _root_.P2MLLL.t00ef6f00 renaming h78 → _p2mH78




set_option maxRecDepth 8192
/-- `writeScaledColumn` leaves strictly-above-diagonal entries (`i < j`)
unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h55
    (coeffs rows : Array (Array Int)) (n k i j : Nat) (hij : i < j) :
    getArrayEntry (writeScaledColumn coeffs rows n k) i j = getArrayEntry coeffs i j := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [_root_.P2MLLL.t00ef6f00.h29]
  · by_cases hrow : i = k
    · subst k
      rw [_root_.P2MLLL.t00ef6f00.h46]
      omega
    · rw [_root_.P2MLLL.t00ef6f00.h47]
      exact hrow
  · intro x hx
    simp at hx
    omega
  · exact hij
open _root_.P2MLLL.t00ef6f00 renaming h55 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn_above
open _root_.P2MLLL.t00ef6f00 renaming h55 → _p2mH55


set_option maxRecDepth 8192
/-- `writeScaledColumn` writes the matrix diagonal entry `(k, k)` into the
coefficient diagonal. -/
 theorem _root_.P2MLLL.t00ef6f00.h57
    (coeffs rows : Array (Array Int)) (n k : Nat)
    (hrow : k < coeffs.size) (hcol : k < coeffs[k]!.size) :
    getArrayEntry (writeScaledColumn coeffs rows n k) k k =
      getArrayEntry rows k k := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [_root_.P2MLLL.t00ef6f00.h32]
  · rw [_root_.P2MLLL.t00ef6f00.h48 _ _ _ _ hrow hcol]
  · intro x hx
    simp at hx
    omega
  · omega
open _root_.P2MLLL.t00ef6f00 renaming h57 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn_diag
open _root_.P2MLLL.t00ef6f00 renaming h57 → _p2mH57


set_option maxRecDepth 8192
/-- Below the current pivot row, `writeScaledColumn` records the current
matrix-column value in the coefficient column. -/
 theorem _root_.P2MLLL.t00ef6f00.h56
    (coeffs rows : Array (Array Int)) (n k i : Nat)
    (hki : k < i) (hi : i < n)
    (hrow : i < coeffs.size) (hcol : k < coeffs[i]!.size) :
    getArrayEntry (writeScaledColumn coeffs rows n k) i k =
      getArrayEntry rows i k := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have hmem : i ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨i - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  have hrow' : i < (setArrayEntry coeffs k k (getArrayEntry rows k k)).size := by
    simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hrow]
  have hcol' :
      k < (setArrayEntry coeffs k k (getArrayEntry rows k k))[i]!.size := by
    unfold setArrayEntry
    rw [_root_.P2MLLL.t00ef6f00.h24 _ (show i ≠ k by omega)]
    exact hcol
  exact _root_.P2MLLL.t00ef6f00.h30
    (List.range' (k + 1) (n - (k + 1)))
    (setArrayEntry coeffs k k (getArrayEntry rows k k)) rows k i
    hmem hnodup hrow' hcol'
open _root_.P2MLLL.t00ef6f00 renaming h56 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn_below
open _root_.P2MLLL.t00ef6f00 renaming h56 → _p2mH56


set_option maxRecDepth 8192
/-- `writeScaledColumn` only updates entries in column `k`; entries in any
other column are unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h54
    (coeffs rows : Array (Array Int)) (n k r c : Nat) (hc : c ≠ k) :
    getArrayEntry (writeScaledColumn coeffs rows n k) r c =
      getArrayEntry coeffs r c := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [_root_.P2MLLL.t00ef6f00.h31 _ _ _ _ _ _ hc]
  by_cases hrow : r = k
  · subst r
    rw [_root_.P2MLLL.t00ef6f00.h46 _ _ _ _ _ hc]
  · rw [_root_.P2MLLL.t00ef6f00.h47]
    exact hrow
open _root_.P2MLLL.t00ef6f00 renaming h54 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn
open _root_.P2MLLL.t00ef6f00 renaming h54 → _p2mH54


set_option maxRecDepth 8192
/-- A `foldl` of `setArrayEntry` writes at column `k` preserves the
outer-array size. -/
 theorem _root_.P2MLLL.t00ef6f00.h27
    (xs : List Nat) (init rows : Array (Array Int)) (k : Nat) :
    (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) init).size =
      init.size := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact _root_.P2MLLL.t00ef6f00.h77 _ _ _ _
open _root_.P2MLLL.t00ef6f00 renaming h27 → Hex.GramSchmidt.Int.foldl_setArrayEntry_size
open _root_.P2MLLL.t00ef6f00 renaming h27 → _p2mH27


set_option maxRecDepth 8192
/-- A `foldl` of `setArrayEntry` writes at column `k` preserves inner row sizes. -/
 theorem _root_.P2MLLL.t00ef6f00.h26
    (xs : List Nat) (init rows : Array (Array Int)) (k r : Nat) :
    (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) init)[r]!.size =
      init[r]!.size := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact _root_.P2MLLL.t00ef6f00.h76 _ _ _ _ _
open _root_.P2MLLL.t00ef6f00 renaming h26 → Hex.GramSchmidt.Int.foldl_setArrayEntry_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h26 → _p2mH26


set_option maxRecDepth 8192
/-- `writeScaledColumn` preserves the outer-array size. -/
 theorem _root_.P2MLLL.t00ef6f00.h84
    (coeffs rows : Array (Array Int)) (n k : Nat) :
    (writeScaledColumn coeffs rows n k).size = coeffs.size := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [_root_.P2MLLL.t00ef6f00.h27]
  exact _root_.P2MLLL.t00ef6f00.h77 _ _ _ _
open _root_.P2MLLL.t00ef6f00 renaming h84 → Hex.GramSchmidt.Int.writeScaledColumn_size
open _root_.P2MLLL.t00ef6f00 renaming h84 → _p2mH84


set_option maxRecDepth 8192
/-- `writeScaledColumn` preserves each inner row's size. -/
 theorem _root_.P2MLLL.t00ef6f00.h83
    (coeffs rows : Array (Array Int)) (n k r : Nat) :
    (writeScaledColumn coeffs rows n k)[r]!.size = coeffs[r]!.size := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [_root_.P2MLLL.t00ef6f00.h26]
  exact _root_.P2MLLL.t00ef6f00.h76 _ _ _ _ _
open _root_.P2MLLL.t00ef6f00 renaming h83 → Hex.GramSchmidt.Int.writeScaledColumn_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h83 → _p2mH83


set_option maxRecDepth 8192
/-- Every entry of the default (empty) integer array reads back as `0`. -/
 theorem _root_.P2MLLL.t00ef6f00.h28 (j : Nat) :
    (default : Array Int)[j]! = 0 := by
  rfl
open _root_.P2MLLL.t00ef6f00 renaming h28 → Hex.GramSchmidt.Int.getArrayEntry_default_row
open _root_.P2MLLL.t00ef6f00 renaming h28 → _p2mH28




section StepScaledRowsBookkeeping

set_option maxRecDepth 8192
/-- After one `stepScaledRows` sweep, rows whose index lies at or below the
current pivot are untouched by the outer fold. -/
 theorem _root_.P2MLLL.t00ef6f00.h51
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hr : r ≤ k) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      getArrayEntry rows r c := by
  show
      (stepScaledRows rows n k pivot prevPivot)[r]![c]! =
        rows[r]![c]!
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  have hnot : r ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hri⟩ := hmem
    omega
  rw [_root_.P2MLLL.t00ef6f00.h60 _ _ _ _ hnot]
open _root_.P2MLLL.t00ef6f00 renaming h51 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_of_row_le
open _root_.P2MLLL.t00ef6f00 renaming h51 → _p2mH51


set_option maxRecDepth 8192
/-- The new row written at trailing index `r` (with `k < r` and `r < n`) by
`stepScaledRows`, expressed in fold form. This is an intermediate
characterisation; downstream lemmas read individual entries via
`getElem!_foldl_set!_*`. -/
 theorem _root_.P2MLLL.t00ef6f00.h80
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r : Nat) (hk : k < r) (hr : r < n) (hrows : r < rows.size) :
    (stepScaledRows rows n k pivot prevPivot)[r]! =
      (List.range' (k + 1) (n - (k + 1))).foldl
        (fun nextRow j =>
          nextRow.set! j
            (Matrix.exactDiv
              (pivot * nextRow[j]! - rows[r]![k]! * getArrayEntry rows k j)
              prevPivot))
        (rows[r]!.set! k 0) := by
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  have hmem : r ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨r - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  rw [_root_.P2MLLL.t00ef6f00.h59 _ _ _ _ hmem hnodup hrows]
  simp [getArrayEntry]
open _root_.P2MLLL.t00ef6f00 renaming h80 → Hex.GramSchmidt.Int.stepScaledRows_row_at_trailing
open _root_.P2MLLL.t00ef6f00 renaming h80 → _p2mH80


set_option maxRecDepth 8192
/-- The pivot column of `stepScaledRows` is cleared at every trailing row. -/
 theorem _root_.P2MLLL.t00ef6f00.h52
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r : Nat) (hk : k < r) (hr : r < n) (hrows : r < rows.size)
    (hk_row : k < rows[r]!.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r k = 0 := by
  show (stepScaledRows rows n k pivot prevPivot)[r]![k]! = 0
  rw [_root_.P2MLLL.t00ef6f00.h80 rows n k pivot prevPivot r hk hr hrows]
  have hnot : k ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hki⟩ := hmem
    omega
  rw [_root_.P2MLLL.t00ef6f00.h62
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - rows[r]![k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hnot]
  grind
open _root_.P2MLLL.t00ef6f00 renaming h52 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_pivot_col
open _root_.P2MLLL.t00ef6f00 renaming h52 → _p2mH52


set_option maxRecDepth 8192
/-- Trailing-column entries of `stepScaledRows` are the fraction-free
Bareiss-style update written by the inner sweep. -/
 theorem _root_.P2MLLL.t00ef6f00.h53
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hkr : k < r) (hr : r < n) (hkc : k < c) (hc : c < n)
    (hrows : r < rows.size) (hcols : c < rows[r]!.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      Matrix.exactDiv
        (pivot * rows[r]![c]! - rows[r]![k]! * getArrayEntry rows k c)
        prevPivot := by
  show
      (stepScaledRows rows n k pivot prevPivot)[r]![c]! =
        Matrix.exactDiv
          (pivot * rows[r]![c]! - rows[r]![k]! * getArrayEntry rows k c)
          prevPivot
  rw [_root_.P2MLLL.t00ef6f00.h80 rows n k pivot prevPivot r hkr hr hrows]
  have hmem : c ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨c - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  have hbound : c < (rows[r]!.set! k 0).size := by
    simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hcols]
  rw [_root_.P2MLLL.t00ef6f00.h61
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - rows[r]![k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hmem hnodup hbound]
  have hck : c ≠ k := by omega
  grind
open _root_.P2MLLL.t00ef6f00 renaming h53 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_trailing
open _root_.P2MLLL.t00ef6f00 renaming h53 → _p2mH53


set_option maxRecDepth 8192
/-- Entries strictly left of the pivot column of `stepScaledRows` are
preserved at every trailing row: the inner sweep only writes the trailing
window `[k+1, n)`, and the explicit pivot-column zeroing only touches
column `k`. -/
 theorem _root_.P2MLLL.t00ef6f00.h50
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hkr : k < r) (hr : r < n) (hc : c < k)
    (hrows : r < rows.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      getArrayEntry rows r c := by
  show
      (stepScaledRows rows n k pivot prevPivot)[r]![c]! = rows[r]![c]!
  rw [_root_.P2MLLL.t00ef6f00.h80 rows n k pivot prevPivot r hkr hr hrows]
  have hnot : c ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hci⟩ := hmem
    omega
  rw [_root_.P2MLLL.t00ef6f00.h62
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - rows[r]![k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hnot]
  have hck : c ≠ k := by omega
  grind
open _root_.P2MLLL.t00ef6f00 renaming h50 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_of_col_lt
open _root_.P2MLLL.t00ef6f00 renaming h50 → _p2mH50


set_option maxRecDepth 8192
/-- The outer-array length of `stepScaledRows` matches the input. The outer
fold only replaces rows already present in `rows` via `Array.set!`, which
preserves array size. -/
 theorem _root_.P2MLLL.t00ef6f00.h82
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int) :
    (stepScaledRows rows n k pivot prevPivot).size = rows.size := by
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  exact _root_.P2MLLL.t00ef6f00.h78 _ _ _
open _root_.P2MLLL.t00ef6f00 renaming h82 → Hex.GramSchmidt.Int.stepScaledRows_size
open _root_.P2MLLL.t00ef6f00 renaming h82 → _p2mH82


set_option maxRecDepth 8192
/-- If the input row storage has the expected square shape, one
`stepScaledRows` sweep preserves every in-bounds row length. -/
 theorem _root_.P2MLLL.t00ef6f00.h81
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (hsize : rows.size = n)
    (hrowsize : ∀ r, r < n → rows[r]!.size = n) :
    ∀ r, r < n → (stepScaledRows rows n k pivot prevPivot)[r]!.size = n := by
  intro r hr
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  let xs := List.range' (k + 1) (n - (k + 1))
  let f : Nat → Array Int → Array Int := fun i sourceRow =>
    (List.range' (k + 1) (n - (k + 1))).foldl
      (fun nextRow j =>
        nextRow.set! j
          (Matrix.exactDiv
            (pivot * nextRow[j]! - sourceRow[k]! * rows[k]![j]!)
            prevPivot))
      (sourceRow.set! k 0)
  by_cases hmem : r ∈ xs
  · have hnodup : xs.Nodup := by
      dsimp [xs]
      exact List.nodup_range'
    have hbound : r < rows.size := by
      rw [hsize]
      exact hr
    rw [_root_.P2MLLL.t00ef6f00.h59 xs rows f r hmem hnodup hbound]
    dsimp [f]
    have hinner_size :=
      _root_.P2MLLL.t00ef6f00.h79
        (List.range' (k + 1) (n - (k + 1)))
        (rows[r]!.set! k 0)
        (fun j nextEntry =>
          Matrix.exactDiv
            (pivot * nextEntry - rows[r]![k]! * getArrayEntry rows k j)
            prevPivot)
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
      hrowsize r hr] at hinner_size ⊢
    exact hinner_size
  · rw [_root_.P2MLLL.t00ef6f00.h60 xs rows f r hmem]
    exact hrowsize r hr
open _root_.P2MLLL.t00ef6f00 renaming h81 → Hex.GramSchmidt.Int.stepScaledRows_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h81 → _p2mH81


set_option maxRecDepth 8192
/-- Per-entry correspondence between the row-mutating array-storage
`stepScaledRows` update and the matrix-storage `Matrix.stepMatrix` update.
Trailing-block entries use the same `Matrix.exactDiv` expression, the pivot
column clears to zero, and entries outside the update region are preserved on
both sides. -/
 theorem _root_.P2MLLL.t00ef6f00.h49
    {n : Nat} (rows : Array (Array Int)) (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int)
    (hentry : ∀ a b : Fin n, getArrayEntry rows a.val b.val = M[a][b])
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n)
    (i j : Fin n) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) i.val j.val =
      (Matrix.stepMatrix M k pivot prevPivot)[i][j] := by
  rcases Nat.lt_or_ge k i.val with hki | hki
  · rcases Nat.lt_or_ge k j.val with hkj | hkj
    · -- Trailing-block update: divide the Bareiss numerator by `prevPivot`.
      have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
      have hcols : j.val < rows[i.val]!.size := by
        rw [hrowsize i.val i.isLt]; exact j.isLt
      have hij_eq : getArrayEntry rows i.val j.val = M[i][j] := hentry i j
      have hcol_eq :
          getArrayEntry rows i.val k =
            M[i][(⟨k, Nat.lt_trans hki i.isLt⟩ : Fin n)] := by
        simpa using hentry i ⟨k, Nat.lt_trans hki i.isLt⟩
      have hrow_eq :
          getArrayEntry rows k j.val =
            M[(⟨k, Nat.lt_trans hkj j.isLt⟩ : Fin n)][j] := by
        simpa using hentry ⟨k, Nat.lt_trans hkj j.isLt⟩ j
      rw [_root_.P2MLLL.t00ef6f00.h53 rows n k pivot prevPivot
            i.val j.val hki i.isLt hkj j.isLt hrows hcols]
      rw [Matrix.stepMatrix_update_eq M k pivot prevPivot i j hki hkj]
      change Matrix.exactDiv
          (pivot * getArrayEntry rows i.val j.val -
            getArrayEntry rows i.val k * getArrayEntry rows k j.val) prevPivot =
        Matrix.exactDiv
          (pivot * M[i][j] -
            M[i][(⟨k, Nat.lt_trans hki i.isLt⟩ : Fin n)] *
              M[(⟨k, Nat.lt_trans hkj j.isLt⟩ : Fin n)][j]) prevPivot
      rw [hij_eq, hcol_eq, hrow_eq]
    · -- Pivot column or strictly-left column at a trailing row.
      rcases Nat.lt_or_eq_of_le hkj with hkj_lt | hkj_eq
      · -- Strictly left of pivot column: entries preserved on both sides.
        have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
        rw [_root_.P2MLLL.t00ef6f00.h50 rows n k pivot prevPivot
              i.val j.val hki i.isLt hkj_lt hrows]
        rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot i j
              (fun h => Nat.not_lt_of_ge hkj h.2)
              (fun h => Nat.ne_of_lt hkj_lt h.2)]
        exact hentry i j
      · -- Pivot column itself: both sides clear to zero.
        have hjk : j.val = k := hkj_eq
        have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
        have hk_row : k < rows[i.val]!.size := by
          rw [hrowsize i.val i.isLt]
          exact Nat.lt_of_lt_of_le hki (Nat.le_of_lt i.isLt)
        have hLHS :
            getArrayEntry (stepScaledRows rows n k pivot prevPivot) i.val j.val = 0 := by
          rw [hjk]
          exact _root_.P2MLLL.t00ef6f00.h52 rows n k pivot prevPivot
            i.val hki i.isLt hrows hk_row
        have hRHS :
            (Matrix.stepMatrix M k pivot prevPivot)[i][j] = 0 :=
          Matrix.stepMatrix_pivot_col_below M k pivot prevPivot i j hki hjk
        rw [hLHS]
        exact hRHS.symm
  · -- Row preserved: at or above pivot row.
    rw [_root_.P2MLLL.t00ef6f00.h51 rows n k pivot prevPivot
          i.val j.val hki]
    rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot i j
          (fun h => Nat.not_lt_of_ge hki h.1)
          (fun h => Nat.not_lt_of_ge hki h.1)]
    exact hentry i j
open _root_.P2MLLL.t00ef6f00 renaming h49 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_matches_stepMatrix
open _root_.P2MLLL.t00ef6f00 renaming h49 → _p2mH49


set_option maxRecDepth 8192
/-- Matrix-level correspondence: one row-mutating `stepScaledRows` array
update, viewed as a matrix via `rowsToMatrix`, equals the corresponding
`Matrix.stepMatrix` update on the matrix view of the same row storage. -/
 theorem _root_.P2MLLL.t00ef6f00.h70
    {n : Nat} (rows : Array (Array Int)) (k : Nat) (pivot prevPivot : Int)
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n) :
    rowsToMatrix (stepScaledRows rows n k pivot prevPivot) n =
      Matrix.stepMatrix (rowsToMatrix rows n) k pivot prevPivot := by
  apply Hex.Matrix.ext_getElem
  intro i j
  have hentry : ∀ a b : Fin n,
      getArrayEntry rows a.val b.val = (rowsToMatrix rows n)[a][b] := by
    intro a b
    rw [rowsToMatrix, Matrix.getElem_ofFn]
  rw [rowsToMatrix, Matrix.getElem_ofFn]
  exact _root_.P2MLLL.t00ef6f00.h49 rows (rowsToMatrix rows n)
    k pivot prevPivot hentry hsize hrowsize i j
open _root_.P2MLLL.t00ef6f00 renaming h70 → Hex.GramSchmidt.Int.rowsToMatrix_stepScaledRows_eq
open _root_.P2MLLL.t00ef6f00 renaming h70 → _p2mH70


end StepScaledRowsBookkeeping
open _root_.P2MLLL.t00ef6f00 renaming h49 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_matches_stepMatrix
open _root_.P2MLLL.t00ef6f00 renaming h49 → _p2mH49
open _root_.P2MLLL.t00ef6f00 renaming h50 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_of_col_lt
open _root_.P2MLLL.t00ef6f00 renaming h50 → _p2mH50
open _root_.P2MLLL.t00ef6f00 renaming h51 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_of_row_le
open _root_.P2MLLL.t00ef6f00 renaming h51 → _p2mH51
open _root_.P2MLLL.t00ef6f00 renaming h52 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_pivot_col
open _root_.P2MLLL.t00ef6f00 renaming h52 → _p2mH52
open _root_.P2MLLL.t00ef6f00 renaming h53 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_trailing
open _root_.P2MLLL.t00ef6f00 renaming h53 → _p2mH53
open _root_.P2MLLL.t00ef6f00 renaming h70 → Hex.GramSchmidt.Int.rowsToMatrix_stepScaledRows_eq
open _root_.P2MLLL.t00ef6f00 renaming h70 → _p2mH70
open _root_.P2MLLL.t00ef6f00 renaming h80 → Hex.GramSchmidt.Int.stepScaledRows_row_at_trailing
open _root_.P2MLLL.t00ef6f00 renaming h80 → _p2mH80
open _root_.P2MLLL.t00ef6f00 renaming h81 → Hex.GramSchmidt.Int.stepScaledRows_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h81 → _p2mH81
open _root_.P2MLLL.t00ef6f00 renaming h82 → Hex.GramSchmidt.Int.stepScaledRows_size
open _root_.P2MLLL.t00ef6f00 renaming h82 → _p2mH82




set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t00ef6f00.h58 (n i j : Nat) :
    getArrayEntry (zeroRows n) i j = 0 := by
  by_cases hi : i < n
  · by_cases hj : j < n <;> simp [zeroRows, getArrayEntry, hi, hj]
  · simp [zeroRows, getArrayEntry, hi, _root_.P2MLLL.t00ef6f00.h28]
open _root_.P2MLLL.t00ef6f00 renaming h58 → Hex.GramSchmidt.Int.getArrayEntry_zeroRows
open _root_.P2MLLL.t00ef6f00 renaming h58 → _p2mH58


set_option maxRecDepth 8192
/-- Outer-array length of the initial Gram row buffer. -/
 theorem _root_.P2MLLL.t00ef6f00.h66 (b : Matrix Int n m) : (gramRows b).size = n := by
  simp [gramRows]
open _root_.P2MLLL.t00ef6f00 renaming h66 → Hex.GramSchmidt.Int.gramRows_size
open _root_.P2MLLL.t00ef6f00 renaming h66 → _p2mH66


set_option maxRecDepth 8192
/-- Inner-row length of each row of the initial Gram row buffer. -/
 theorem _root_.P2MLLL.t00ef6f00.h65 (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    (gramRows b)[r]!.size = n := by
  simp [gramRows, hr]
open _root_.P2MLLL.t00ef6f00 renaming h65 → Hex.GramSchmidt.Int.gramRows_row_size
open _root_.P2MLLL.t00ef6f00 renaming h65 → _p2mH65


set_option maxRecDepth 8192
/-- Outer-array length of the initial coefficient buffer. -/
 theorem _root_.P2MLLL.t00ef6f00.h86 (n : Nat) : (zeroRows n).size = n := by
  simp [zeroRows]
open _root_.P2MLLL.t00ef6f00 renaming h86 → Hex.GramSchmidt.Int.zeroRows_size
open _root_.P2MLLL.t00ef6f00 renaming h86 → _p2mH86


set_option maxRecDepth 8192
/-- Inner-row length of each row of the initial coefficient buffer. -/
 theorem _root_.P2MLLL.t00ef6f00.h85 (n : Nat) (r : Nat) (hr : r < n) :
    (zeroRows n)[r]!.size = n := by
  simp [zeroRows, hr]
open _root_.P2MLLL.t00ef6f00 renaming h85 → Hex.GramSchmidt.Int.zeroRows_row_size
open _root_.P2MLLL.t00ef6f00 renaming h85 → _p2mH85


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t00ef6f00.h35
    (n fuel : Nat) (state : ScaledCoeffArrayState)
    (hcoeffs : ∀ i j, i < j → getArrayEntry state.coeffs i j = 0)
    (i j : Nat) (hij : i < j) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state).coeffs i j = 0 := by
  induction fuel generalizing state with
  | zero =>
      exact hcoeffs i j hij
  | succ fuel ih =>
      rw [scaledCoeffArrayLoop]
      by_cases hstep : state.step < n
      · simp only [hstep, ↓reduceIte]
        by_cases hnext : state.step + 1 < n
        · simp only [hnext, ↓reduceIte]
          by_cases hpivot : getArrayEntry state.matrix state.step state.step = 0
          · simp only [hpivot, ↓reduceIte]
            rw [_root_.P2MLLL.t00ef6f00.h55 _ _ _ _ _ _ hij]
            exact hcoeffs i j hij
          · simp only [hpivot, ↓reduceIte]
            exact ih
              { step := state.step + 1
                matrix := stepScaledRows state.matrix n state.step
                  (getArrayEntry state.matrix state.step state.step) state.prevPivot
                coeffs := writeScaledColumn state.coeffs state.matrix n state.step
                prevPivot := getArrayEntry state.matrix state.step state.step }
              (by
                intro r c hrc
                rw [_root_.P2MLLL.t00ef6f00.h55 _ _ _ _ _ _ hrc]
                exact hcoeffs r c hrc)
        · simp only [hnext, ↓reduceIte]
          rw [_root_.P2MLLL.t00ef6f00.h55 _ _ _ _ _ _ hij]
          exact hcoeffs i j hij
      · simp only [hstep, ↓reduceIte]
        exact hcoeffs i j hij
open _root_.P2MLLL.t00ef6f00 renaming h35 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffArrayLoop_above
open _root_.P2MLLL.t00ef6f00 renaming h35 → _p2mH35


set_option maxRecDepth 8192
/-- Once a coefficient column lies strictly before the current loop step, later
`scaledCoeffArrayLoop` iterations do not rewrite that column. -/
 theorem _root_.P2MLLL.t00ef6f00.h36
    (n fuel : Nat) (state : ScaledCoeffArrayState) (i j : Nat)
    (hj : j < state.step) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state).coeffs i j =
      getArrayEntry state.coeffs i j := by
  induction fuel generalizing state with
  | zero =>
      rfl
  | succ fuel ih =>
      rw [scaledCoeffArrayLoop]
      by_cases hstep : state.step < n
      · simp only [hstep, ↓reduceIte]
        by_cases hnext : state.step + 1 < n
        · simp only [hnext, ↓reduceIte]
          by_cases hpivot : getArrayEntry state.matrix state.step state.step = 0
          · simp only [hpivot, ↓reduceIte]
            rw [_root_.P2MLLL.t00ef6f00.h54]
            omega
          · simp only [hpivot, ↓reduceIte]
            rw [ih]
            · rw [_root_.P2MLLL.t00ef6f00.h54]
              omega
            · show j < state.step + 1
              omega
        · simp only [hnext, ↓reduceIte]
          rw [_root_.P2MLLL.t00ef6f00.h54]
          omega
      · simp only [hstep, ↓reduceIte]
open _root_.P2MLLL.t00ef6f00 renaming h36 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step
open _root_.P2MLLL.t00ef6f00 renaming h36 → _p2mH36










set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t00ef6f00.h42
    (cols : List Nat) (rows gram : Array (Array Int)) (row i j : Nat)
    (hij : i < j) (hcols : ∀ c ∈ cols, c ≤ row) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        i j =
      getArrayEntry rows i j := by
  induction cols generalizing rows with
  | nil =>
      simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      have hcols_tail : ∀ c ∈ cols, c ≤ row := by
        intro c hc
        exact hcols c (List.mem_cons_of_mem col hc)
      rw [ih _ hcols_tail]
      by_cases hrow : i = row
      · subst row
        have hcol_le : col ≤ i := hcols col (by simp)
        rw [_root_.P2MLLL.t00ef6f00.h46]
        omega
      · rw [_root_.P2MLLL.t00ef6f00.h47]
        exact hrow
open _root_.P2MLLL.t00ef6f00 renaming h42 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_upper
open _root_.P2MLLL.t00ef6f00 renaming h42 → _p2mH42


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t00ef6f00.h45
    (rowList : List Nat) (rows gram : Array (Array Int)) (i j : Nat)
    (hij : i < j) :
    getArrayEntry
        (rowList.foldl
          (fun next row =>
            (List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              next) rows)
        i j =
      getArrayEntry rows i j := by
  induction rowList generalizing rows with
  | nil =>
      simp
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      rw [ih _, _root_.P2MLLL.t00ef6f00.h42]
      · exact hij
      · intro c hc
        rw [List.mem_range'] at hc
        omega
open _root_.P2MLLL.t00ef6f00 renaming h45 → Hex.GramSchmidt.Int.getArrayEntry_schurRowLoop_upper
open _root_.P2MLLL.t00ef6f00 renaming h45 → _p2mH45


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t00ef6f00.h37
    (b : Matrix Int n m) (i j : Nat) (hij : i < j) :
    getArrayEntry (scaledCoeffRowsSchur b) i j = 0 := by
  simp [scaledCoeffRowsSchur]
  rw [_root_.P2MLLL.t00ef6f00.h45]
  · exact _root_.P2MLLL.t00ef6f00.h58 n i j
  · exact hij
open _root_.P2MLLL.t00ef6f00 renaming h37 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_upper
open _root_.P2MLLL.t00ef6f00 renaming h37 → _p2mH37


set_option maxRecDepth 8192
/-- The Schur column loop fixes the active row `row`: cells in any other row
are untouched, irrespective of which columns the loop visits. -/
 theorem _root_.P2MLLL.t00ef6f00.h41
    (cols : List Nat) (rows gram : Array (Array Int)) (row r c : Nat)
    (hr : r ≠ row) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        r c =
      getArrayEntry rows r c := by
  induction cols generalizing rows with
  | nil => simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact _root_.P2MLLL.t00ef6f00.h47 rows row col r c _ hr
open _root_.P2MLLL.t00ef6f00 renaming h41 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_row_ne
open _root_.P2MLLL.t00ef6f00 renaming h41 → _p2mH41


set_option maxRecDepth 8192
/-- Row-completion frame lemma. The outer Schur row loop only writes to rows
listed in `rowList`; cells in rows not in `rowList` retain their initial
values. In particular, once row `i` has been processed by the row loop, the
remaining row iterations preserve every cell `(i, ·)`. -/
 theorem _root_.P2MLLL.t00ef6f00.h44
    (rowList : List Nat) (rows gram : Array (Array Int)) (i j : Nat)
    (hi : i ∉ rowList) :
    getArrayEntry
        (rowList.foldl
          (fun next row =>
            (List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              next) rows)
        i j =
      getArrayEntry rows i j := by
  induction rowList generalizing rows with
  | nil => simp
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      have hi_ne : i ≠ row := fun h => hi (h ▸ List.mem_cons_self)
      have hi_tail : i ∉ rowList := fun h => hi (List.mem_cons_of_mem row h)
      rw [ih _ hi_tail]
      exact _root_.P2MLLL.t00ef6f00.h41 _ rows gram row i j hi_ne
open _root_.P2MLLL.t00ef6f00 renaming h44 → Hex.GramSchmidt.Int.getArrayEntry_schurRowLoop_row_not_mem
open _root_.P2MLLL.t00ef6f00 renaming h44 → _p2mH44


set_option maxRecDepth 8192
/-- Column-loop stability for the `(row, 0)` cell when the loop never visits
column `0`. Subsequent column writes at a different column keep the cell
unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h40
    (cols : List Nat) (rows gram : Array (Array Int)) (row : Nat)
    (hzero : 0 ∉ cols) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        row 0 =
      getArrayEntry rows row 0 := by
  induction cols generalizing rows with
  | nil => simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      have h_col_ne : col ≠ 0 := fun h => hzero (h ▸ List.mem_cons_self)
      have h_tail : 0 ∉ cols := fun h => hzero (List.mem_cons_of_mem col h)
      rw [ih _ h_tail]
      exact _root_.P2MLLL.t00ef6f00.h46 rows row col 0 _ h_col_ne.symm
open _root_.P2MLLL.t00ef6f00 renaming h40 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_col_zero_preserve
open _root_.P2MLLL.t00ef6f00 renaming h40 → _p2mH40


set_option maxRecDepth 8192
/-- Column-loop stability for a cell `(row, col_target)` when the loop never
visits `col_target`. Subsequent column writes at different columns keep
the cell unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h38
    (cols : List Nat) (rows gram : Array (Array Int)) (row col_target : Nat)
    (h_not_mem : col_target ∉ cols) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        row col_target =
      getArrayEntry rows row col_target := by
  induction cols generalizing rows with
  | nil => simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      have h_col_ne : col ≠ col_target :=
        fun h => h_not_mem (h ▸ List.mem_cons_self)
      have h_tail : col_target ∉ cols :=
        fun h => h_not_mem (List.mem_cons_of_mem col h)
      rw [ih _ h_tail]
      exact _root_.P2MLLL.t00ef6f00.h46 rows row col col_target _
        (fun h => h_col_ne h.symm)
open _root_.P2MLLL.t00ef6f00 renaming h38 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_col_not_mem
open _root_.P2MLLL.t00ef6f00 renaming h38 → _p2mH38


set_option maxRecDepth 8192
/-- Single-row column-loop dispatch for column `0`. When `0` appears in
`cols`, the column loop ultimately writes `getArrayEntry gram row 0` into the
`(row, 0)` slot. Because the `j = 0` branch of `schurScaledCoeffEntry`
returns the gram entry directly, this value is independent of which other
columns are written before or after. -/
 theorem _root_.P2MLLL.t00ef6f00.h39
    (cols : List Nat) (rows gram : Array (Array Int)) (row : Nat)
    (hzero : 0 ∈ cols)
    (hrow : row < rows.size) (hcol : 0 < rows[row]!.size) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        row 0 =
      getArrayEntry gram row 0 := by
  induction cols generalizing rows with
  | nil => exact absurd hzero (List.not_mem_nil)
  | cons col cols ih =>
      simp only [List.foldl_cons]
      by_cases h_zero_in_tail : 0 ∈ cols
      · have hrow' :
            row < (setArrayEntry rows row col
                (schurScaledCoeffEntry rows gram row col)).size := by
          rw [_root_.P2MLLL.t00ef6f00.h77]; exact hrow
        have hcol' :
            0 < (setArrayEntry rows row col
                (schurScaledCoeffEntry rows gram row col))[row]!.size := by
          rw [_root_.P2MLLL.t00ef6f00.h76]; exact hcol
        exact ih _ h_zero_in_tail hrow' hcol'
      · have h_col_eq : col = 0 := by
          rcases List.mem_cons.mp hzero with h | h
          · exact h.symm
          · exact (h_zero_in_tail h).elim
        subst h_col_eq
        rw [_root_.P2MLLL.t00ef6f00.h40 _ _ _ _ h_zero_in_tail,
          _root_.P2MLLL.t00ef6f00.h48 _ _ _ _ hrow hcol]
        simp [schurScaledCoeffEntry]
open _root_.P2MLLL.t00ef6f00 renaming h39 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h39 → _p2mH39


set_option maxRecDepth 8192
/-- Size preservation: the Schur column loop keeps the outer-array length. -/
 theorem _root_.P2MLLL.t00ef6f00.h73
    (cols : List Nat) (rows gram : Array (Array Int)) (row : Nat) :
    (cols.foldl
        (fun next col =>
          setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows).size =
      rows.size := by
  induction cols generalizing rows with
  | nil => rfl
  | cons col cols ih => simp only [List.foldl_cons]; rw [ih]; exact _root_.P2MLLL.t00ef6f00.h77 _ _ _ _
open _root_.P2MLLL.t00ef6f00 renaming h73 → Hex.GramSchmidt.Int.schurColumnLoop_size
open _root_.P2MLLL.t00ef6f00 renaming h73 → _p2mH73


set_option maxRecDepth 8192
/-- Size preservation: the Schur column loop keeps each inner row's length. -/
 theorem _root_.P2MLLL.t00ef6f00.h72
    (cols : List Nat) (rows gram : Array (Array Int)) (row r : Nat) :
    (cols.foldl
        (fun next col =>
          setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)[r]!.size =
      rows[r]!.size := by
  induction cols generalizing rows with
  | nil => rfl
  | cons col cols ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact _root_.P2MLLL.t00ef6f00.h76 _ _ _ _ _
open _root_.P2MLLL.t00ef6f00 renaming h72 → Hex.GramSchmidt.Int.schurColumnLoop_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h72 → _p2mH72


set_option maxRecDepth 8192
/-- Size preservation: the Schur row loop keeps the outer-array length. -/
 theorem _root_.P2MLLL.t00ef6f00.h75
    (rowList : List Nat) (rows gram : Array (Array Int)) :
    (rowList.foldl
      (fun next row =>
        (List.range' 0 (row + 1)).foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
          next) rows).size =
      rows.size := by
  induction rowList generalizing rows with
  | nil => rfl
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact _root_.P2MLLL.t00ef6f00.h73 _ _ _ _
open _root_.P2MLLL.t00ef6f00 renaming h75 → Hex.GramSchmidt.Int.schurRowLoop_size
open _root_.P2MLLL.t00ef6f00 renaming h75 → _p2mH75


set_option maxRecDepth 8192
/-- Size preservation: the Schur row loop keeps each inner row's length. -/
 theorem _root_.P2MLLL.t00ef6f00.h74
    (rowList : List Nat) (rows gram : Array (Array Int)) (r : Nat) :
    (rowList.foldl
      (fun next row =>
        (List.range' 0 (row + 1)).foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
          next) rows)[r]!.size =
      rows[r]!.size := by
  induction rowList generalizing rows with
  | nil => rfl
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact _root_.P2MLLL.t00ef6f00.h72 _ _ _ _ _
open _root_.P2MLLL.t00ef6f00 renaming h74 → Hex.GramSchmidt.Int.schurRowLoop_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h74 → _p2mH74


set_option maxRecDepth 8192
/-- Outer-array length of the per-row Schur kernel: the row buffer is
allocated as `zeroRows n` and the row loop writes via `setArrayEntry`,
which preserves outer-array size. -/
 theorem _root_.P2MLLL.t00ef6f00.h71 (b : Matrix Int n m) :
    (scaledCoeffRowsSchur b).size = n := by
  simp [scaledCoeffRowsSchur]
  rw [_root_.P2MLLL.t00ef6f00.h75]
  exact _root_.P2MLLL.t00ef6f00.h86 n
open _root_.P2MLLL.t00ef6f00 renaming h71 → Hex.GramSchmidt.Int.scaledCoeffRowsSchur_size
open _root_.P2MLLL.t00ef6f00 renaming h71 → _p2mH71


set_option maxRecDepth 8192
/-- Row-loop dispatch for the `(i, 0)` boundary. If `i ∈ rowList` and the
initial row buffer is large enough at row `i`, the Schur row loop writes the
`(i, 0)` cell to `getArrayEntry gram i 0` (via the inner column loop) and
leaves it untouched in subsequent row iterations. -/
 theorem _root_.P2MLLL.t00ef6f00.h43
    (rowList : List Nat) (rows gram : Array (Array Int)) (i : Nat)
    (hi : i ∈ rowList) (hrow : i < rows.size) (hcol : 0 < rows[i]!.size) :
    getArrayEntry
        (rowList.foldl
          (fun next row =>
            (List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              next) rows)
        i 0 =
      getArrayEntry gram i 0 := by
  induction rowList generalizing rows with
  | nil => exact absurd hi List.not_mem_nil
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      by_cases h_i_in_tail : i ∈ rowList
      · -- Recurse into the tail, deriving size hypotheses via the column-loop
        -- size-preservation lemmas.
        have h_size :
            i < ((List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              rows).size := by
          rw [_root_.P2MLLL.t00ef6f00.h73]; exact hrow
        have h_row_size :
            0 < ((List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              rows)[i]!.size := by
          rw [_root_.P2MLLL.t00ef6f00.h72]; exact hcol
        exact ih _ h_i_in_tail h_size h_row_size
      · -- i is exactly the current `row`. The column loop visits `0`
        -- (`List.range' 0 (row + 1)` contains `0`), writes the gram entry
        -- there, and tail row iterations preserve `(i, 0)`.
        have h_i_eq : i = row := by
          rcases List.mem_cons.mp hi with h | h
          · exact h
          · exact (h_i_in_tail h).elim
        subst h_i_eq
        rw [_root_.P2MLLL.t00ef6f00.h44 _ _ _ _ _ h_i_in_tail]
        apply _root_.P2MLLL.t00ef6f00.h39 _ _ _ _ _ hrow hcol
        rw [List.mem_range']
        exact ⟨0, Nat.succ_pos _, by simp⟩
open _root_.P2MLLL.t00ef6f00 renaming h43 → Hex.GramSchmidt.Int.getArrayEntry_schurRowLoop_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h43 → _p2mH43


end GramSchmidt.Int
open _root_.P2MLLL.t00ef6f00 renaming h24 → Hex.GramSchmidt.Int.array_getElem!_set!_ne
open _root_.P2MLLL.t00ef6f00 renaming h24 → _p2mH24
open _root_.P2MLLL.t00ef6f00 renaming h25 → Hex.GramSchmidt.Int.array_getElem!_set!_same
open _root_.P2MLLL.t00ef6f00 renaming h25 → _p2mH25
open _root_.P2MLLL.t00ef6f00 renaming h26 → Hex.GramSchmidt.Int.foldl_setArrayEntry_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h26 → _p2mH26
open _root_.P2MLLL.t00ef6f00 renaming h27 → Hex.GramSchmidt.Int.foldl_setArrayEntry_size
open _root_.P2MLLL.t00ef6f00 renaming h27 → _p2mH27
open _root_.P2MLLL.t00ef6f00 renaming h28 → Hex.GramSchmidt.Int.getArrayEntry_default_row
open _root_.P2MLLL.t00ef6f00 renaming h28 → _p2mH28
open _root_.P2MLLL.t00ef6f00 renaming h29 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_col_above
open _root_.P2MLLL.t00ef6f00 renaming h29 → _p2mH29
open _root_.P2MLLL.t00ef6f00 renaming h30 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_col_mem
open _root_.P2MLLL.t00ef6f00 renaming h30 → _p2mH30
open _root_.P2MLLL.t00ef6f00 renaming h31 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_col_ne
open _root_.P2MLLL.t00ef6f00 renaming h31 → _p2mH31
open _root_.P2MLLL.t00ef6f00 renaming h32 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_row_ne
open _root_.P2MLLL.t00ef6f00 renaming h32 → _p2mH32
open _root_.P2MLLL.t00ef6f00 renaming h33 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_row_notMem
open _root_.P2MLLL.t00ef6f00 renaming h33 → _p2mH33
open _root_.P2MLLL.t00ef6f00 renaming h34 → Hex.GramSchmidt.Int.getArrayEntry_gramRows
open _root_.P2MLLL.t00ef6f00 renaming h34 → _p2mH34
open _root_.P2MLLL.t00ef6f00 renaming h35 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffArrayLoop_above
open _root_.P2MLLL.t00ef6f00 renaming h35 → _p2mH35
open _root_.P2MLLL.t00ef6f00 renaming h36 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step
open _root_.P2MLLL.t00ef6f00 renaming h36 → _p2mH36
open _root_.P2MLLL.t00ef6f00 renaming h37 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_upper
open _root_.P2MLLL.t00ef6f00 renaming h37 → _p2mH37
open _root_.P2MLLL.t00ef6f00 renaming h38 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_col_not_mem
open _root_.P2MLLL.t00ef6f00 renaming h38 → _p2mH38
open _root_.P2MLLL.t00ef6f00 renaming h39 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h39 → _p2mH39
open _root_.P2MLLL.t00ef6f00 renaming h40 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_col_zero_preserve
open _root_.P2MLLL.t00ef6f00 renaming h40 → _p2mH40
open _root_.P2MLLL.t00ef6f00 renaming h41 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_row_ne
open _root_.P2MLLL.t00ef6f00 renaming h41 → _p2mH41
open _root_.P2MLLL.t00ef6f00 renaming h42 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_upper
open _root_.P2MLLL.t00ef6f00 renaming h42 → _p2mH42
open _root_.P2MLLL.t00ef6f00 renaming h43 → Hex.GramSchmidt.Int.getArrayEntry_schurRowLoop_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h43 → _p2mH43
open _root_.P2MLLL.t00ef6f00 renaming h44 → Hex.GramSchmidt.Int.getArrayEntry_schurRowLoop_row_not_mem
open _root_.P2MLLL.t00ef6f00 renaming h44 → _p2mH44
open _root_.P2MLLL.t00ef6f00 renaming h45 → Hex.GramSchmidt.Int.getArrayEntry_schurRowLoop_upper
open _root_.P2MLLL.t00ef6f00 renaming h45 → _p2mH45
open _root_.P2MLLL.t00ef6f00 renaming h46 → Hex.GramSchmidt.Int.getArrayEntry_setArrayEntry_of_col_ne
open _root_.P2MLLL.t00ef6f00 renaming h46 → _p2mH46
open _root_.P2MLLL.t00ef6f00 renaming h47 → Hex.GramSchmidt.Int.getArrayEntry_setArrayEntry_of_row_ne
open _root_.P2MLLL.t00ef6f00 renaming h47 → _p2mH47
open _root_.P2MLLL.t00ef6f00 renaming h48 → Hex.GramSchmidt.Int.getArrayEntry_setArrayEntry_self
open _root_.P2MLLL.t00ef6f00 renaming h48 → _p2mH48
open _root_.P2MLLL.t00ef6f00 renaming h49 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_matches_stepMatrix
open _root_.P2MLLL.t00ef6f00 renaming h49 → _p2mH49
open _root_.P2MLLL.t00ef6f00 renaming h50 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_of_col_lt
open _root_.P2MLLL.t00ef6f00 renaming h50 → _p2mH50
open _root_.P2MLLL.t00ef6f00 renaming h51 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_of_row_le
open _root_.P2MLLL.t00ef6f00 renaming h51 → _p2mH51
open _root_.P2MLLL.t00ef6f00 renaming h52 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_pivot_col
open _root_.P2MLLL.t00ef6f00 renaming h52 → _p2mH52
open _root_.P2MLLL.t00ef6f00 renaming h53 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_trailing
open _root_.P2MLLL.t00ef6f00 renaming h53 → _p2mH53
open _root_.P2MLLL.t00ef6f00 renaming h54 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn
open _root_.P2MLLL.t00ef6f00 renaming h54 → _p2mH54
open _root_.P2MLLL.t00ef6f00 renaming h55 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn_above
open _root_.P2MLLL.t00ef6f00 renaming h55 → _p2mH55
open _root_.P2MLLL.t00ef6f00 renaming h56 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn_below
open _root_.P2MLLL.t00ef6f00 renaming h56 → _p2mH56
open _root_.P2MLLL.t00ef6f00 renaming h57 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn_diag
open _root_.P2MLLL.t00ef6f00 renaming h57 → _p2mH57
open _root_.P2MLLL.t00ef6f00 renaming h58 → Hex.GramSchmidt.Int.getArrayEntry_zeroRows
open _root_.P2MLLL.t00ef6f00 renaming h58 → _p2mH58
open _root_.P2MLLL.t00ef6f00 renaming h59 → Hex.GramSchmidt.Int.getElem!_foldl_modify_of_mem_nodup
open _root_.P2MLLL.t00ef6f00 renaming h59 → _p2mH59
open _root_.P2MLLL.t00ef6f00 renaming h60 → Hex.GramSchmidt.Int.getElem!_foldl_modify_of_notMem
open _root_.P2MLLL.t00ef6f00 renaming h60 → _p2mH60
open _root_.P2MLLL.t00ef6f00 renaming h61 → Hex.GramSchmidt.Int.getElem!_foldl_setSelf_of_mem_nodup
open _root_.P2MLLL.t00ef6f00 renaming h61 → _p2mH61
open _root_.P2MLLL.t00ef6f00 renaming h62 → Hex.GramSchmidt.Int.getElem!_foldl_setSelf_of_notMem
open _root_.P2MLLL.t00ef6f00 renaming h62 → _p2mH62
open _root_.P2MLLL.t00ef6f00 renaming h63 → Hex.GramSchmidt.Int.getElem!_modify_ne
open _root_.P2MLLL.t00ef6f00 renaming h63 → _p2mH63
open _root_.P2MLLL.t00ef6f00 renaming h64 → Hex.GramSchmidt.Int.getElem!_modify_self
open _root_.P2MLLL.t00ef6f00 renaming h64 → _p2mH64
open _root_.P2MLLL.t00ef6f00 renaming h65 → Hex.GramSchmidt.Int.gramRows_row_size
open _root_.P2MLLL.t00ef6f00 renaming h65 → _p2mH65
open _root_.P2MLLL.t00ef6f00 renaming h66 → Hex.GramSchmidt.Int.gramRows_size
open _root_.P2MLLL.t00ef6f00 renaming h66 → _p2mH66
open _root_.P2MLLL.t00ef6f00 renaming h67 → Hex.GramSchmidt.Int.modify_eq_set!
open _root_.P2MLLL.t00ef6f00 renaming h67 → _p2mH67
open _root_.P2MLLL.t00ef6f00 renaming h68 → Hex.GramSchmidt.Int.modify_size
open _root_.P2MLLL.t00ef6f00 renaming h68 → _p2mH68
open _root_.P2MLLL.t00ef6f00 renaming h69 → Hex.GramSchmidt.Int.rowsToMatrix_gramRows
open _root_.P2MLLL.t00ef6f00 renaming h69 → _p2mH69
open _root_.P2MLLL.t00ef6f00 renaming h70 → Hex.GramSchmidt.Int.rowsToMatrix_stepScaledRows_eq
open _root_.P2MLLL.t00ef6f00 renaming h70 → _p2mH70
open _root_.P2MLLL.t00ef6f00 renaming h71 → Hex.GramSchmidt.Int.scaledCoeffRowsSchur_size
open _root_.P2MLLL.t00ef6f00 renaming h71 → _p2mH71
open _root_.P2MLLL.t00ef6f00 renaming h72 → Hex.GramSchmidt.Int.schurColumnLoop_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h72 → _p2mH72
open _root_.P2MLLL.t00ef6f00 renaming h73 → Hex.GramSchmidt.Int.schurColumnLoop_size
open _root_.P2MLLL.t00ef6f00 renaming h73 → _p2mH73
open _root_.P2MLLL.t00ef6f00 renaming h74 → Hex.GramSchmidt.Int.schurRowLoop_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h74 → _p2mH74
open _root_.P2MLLL.t00ef6f00 renaming h75 → Hex.GramSchmidt.Int.schurRowLoop_size
open _root_.P2MLLL.t00ef6f00 renaming h75 → _p2mH75
open _root_.P2MLLL.t00ef6f00 renaming h76 → Hex.GramSchmidt.Int.setArrayEntry_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h76 → _p2mH76
open _root_.P2MLLL.t00ef6f00 renaming h77 → Hex.GramSchmidt.Int.setArrayEntry_size
open _root_.P2MLLL.t00ef6f00 renaming h77 → _p2mH77
open _root_.P2MLLL.t00ef6f00 renaming h78 → Hex.GramSchmidt.Int.size_foldl_modify
open _root_.P2MLLL.t00ef6f00 renaming h78 → _p2mH78
open _root_.P2MLLL.t00ef6f00 renaming h79 → Hex.GramSchmidt.Int.size_foldl_setSelf
open _root_.P2MLLL.t00ef6f00 renaming h79 → _p2mH79
open _root_.P2MLLL.t00ef6f00 renaming h80 → Hex.GramSchmidt.Int.stepScaledRows_row_at_trailing
open _root_.P2MLLL.t00ef6f00 renaming h80 → _p2mH80
open _root_.P2MLLL.t00ef6f00 renaming h81 → Hex.GramSchmidt.Int.stepScaledRows_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h81 → _p2mH81
open _root_.P2MLLL.t00ef6f00 renaming h82 → Hex.GramSchmidt.Int.stepScaledRows_size
open _root_.P2MLLL.t00ef6f00 renaming h82 → _p2mH82
open _root_.P2MLLL.t00ef6f00 renaming h83 → Hex.GramSchmidt.Int.writeScaledColumn_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h83 → _p2mH83
open _root_.P2MLLL.t00ef6f00 renaming h84 → Hex.GramSchmidt.Int.writeScaledColumn_size
open _root_.P2MLLL.t00ef6f00 renaming h84 → _p2mH84
open _root_.P2MLLL.t00ef6f00 renaming h85 → Hex.GramSchmidt.Int.zeroRows_row_size
open _root_.P2MLLL.t00ef6f00 renaming h85 → _p2mH85
open _root_.P2MLLL.t00ef6f00 renaming h86 → Hex.GramSchmidt.Int.zeroRows_size
open _root_.P2MLLL.t00ef6f00 renaming h86 → _p2mH86

end Hex
open _root_.P2MLLL.t00ef6f00 renaming h24 → Hex.GramSchmidt.Int.array_getElem!_set!_ne
open _root_.P2MLLL.t00ef6f00 renaming h24 → _p2mH24
open _root_.P2MLLL.t00ef6f00 renaming h25 → Hex.GramSchmidt.Int.array_getElem!_set!_same
open _root_.P2MLLL.t00ef6f00 renaming h25 → _p2mH25
open _root_.P2MLLL.t00ef6f00 renaming h26 → Hex.GramSchmidt.Int.foldl_setArrayEntry_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h26 → _p2mH26
open _root_.P2MLLL.t00ef6f00 renaming h27 → Hex.GramSchmidt.Int.foldl_setArrayEntry_size
open _root_.P2MLLL.t00ef6f00 renaming h27 → _p2mH27
open _root_.P2MLLL.t00ef6f00 renaming h28 → Hex.GramSchmidt.Int.getArrayEntry_default_row
open _root_.P2MLLL.t00ef6f00 renaming h28 → _p2mH28
open _root_.P2MLLL.t00ef6f00 renaming h29 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_col_above
open _root_.P2MLLL.t00ef6f00 renaming h29 → _p2mH29
open _root_.P2MLLL.t00ef6f00 renaming h30 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_col_mem
open _root_.P2MLLL.t00ef6f00 renaming h30 → _p2mH30
open _root_.P2MLLL.t00ef6f00 renaming h31 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_col_ne
open _root_.P2MLLL.t00ef6f00 renaming h31 → _p2mH31
open _root_.P2MLLL.t00ef6f00 renaming h32 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_row_ne
open _root_.P2MLLL.t00ef6f00 renaming h32 → _p2mH32
open _root_.P2MLLL.t00ef6f00 renaming h33 → Hex.GramSchmidt.Int.getArrayEntry_foldl_setArrayEntry_row_notMem
open _root_.P2MLLL.t00ef6f00 renaming h33 → _p2mH33
open _root_.P2MLLL.t00ef6f00 renaming h34 → Hex.GramSchmidt.Int.getArrayEntry_gramRows
open _root_.P2MLLL.t00ef6f00 renaming h34 → _p2mH34
open _root_.P2MLLL.t00ef6f00 renaming h35 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffArrayLoop_above
open _root_.P2MLLL.t00ef6f00 renaming h35 → _p2mH35
open _root_.P2MLLL.t00ef6f00 renaming h36 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step
open _root_.P2MLLL.t00ef6f00 renaming h36 → _p2mH36
open _root_.P2MLLL.t00ef6f00 renaming h37 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_upper
open _root_.P2MLLL.t00ef6f00 renaming h37 → _p2mH37
open _root_.P2MLLL.t00ef6f00 renaming h38 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_col_not_mem
open _root_.P2MLLL.t00ef6f00 renaming h38 → _p2mH38
open _root_.P2MLLL.t00ef6f00 renaming h39 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h39 → _p2mH39
open _root_.P2MLLL.t00ef6f00 renaming h40 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_col_zero_preserve
open _root_.P2MLLL.t00ef6f00 renaming h40 → _p2mH40
open _root_.P2MLLL.t00ef6f00 renaming h41 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_row_ne
open _root_.P2MLLL.t00ef6f00 renaming h41 → _p2mH41
open _root_.P2MLLL.t00ef6f00 renaming h42 → Hex.GramSchmidt.Int.getArrayEntry_schurColumnLoop_upper
open _root_.P2MLLL.t00ef6f00 renaming h42 → _p2mH42
open _root_.P2MLLL.t00ef6f00 renaming h43 → Hex.GramSchmidt.Int.getArrayEntry_schurRowLoop_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h43 → _p2mH43
open _root_.P2MLLL.t00ef6f00 renaming h44 → Hex.GramSchmidt.Int.getArrayEntry_schurRowLoop_row_not_mem
open _root_.P2MLLL.t00ef6f00 renaming h44 → _p2mH44
open _root_.P2MLLL.t00ef6f00 renaming h45 → Hex.GramSchmidt.Int.getArrayEntry_schurRowLoop_upper
open _root_.P2MLLL.t00ef6f00 renaming h45 → _p2mH45
open _root_.P2MLLL.t00ef6f00 renaming h46 → Hex.GramSchmidt.Int.getArrayEntry_setArrayEntry_of_col_ne
open _root_.P2MLLL.t00ef6f00 renaming h46 → _p2mH46
open _root_.P2MLLL.t00ef6f00 renaming h47 → Hex.GramSchmidt.Int.getArrayEntry_setArrayEntry_of_row_ne
open _root_.P2MLLL.t00ef6f00 renaming h47 → _p2mH47
open _root_.P2MLLL.t00ef6f00 renaming h48 → Hex.GramSchmidt.Int.getArrayEntry_setArrayEntry_self
open _root_.P2MLLL.t00ef6f00 renaming h48 → _p2mH48
open _root_.P2MLLL.t00ef6f00 renaming h49 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_matches_stepMatrix
open _root_.P2MLLL.t00ef6f00 renaming h49 → _p2mH49
open _root_.P2MLLL.t00ef6f00 renaming h50 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_of_col_lt
open _root_.P2MLLL.t00ef6f00 renaming h50 → _p2mH50
open _root_.P2MLLL.t00ef6f00 renaming h51 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_of_row_le
open _root_.P2MLLL.t00ef6f00 renaming h51 → _p2mH51
open _root_.P2MLLL.t00ef6f00 renaming h52 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_pivot_col
open _root_.P2MLLL.t00ef6f00 renaming h52 → _p2mH52
open _root_.P2MLLL.t00ef6f00 renaming h53 → Hex.GramSchmidt.Int.getArrayEntry_stepScaledRows_trailing
open _root_.P2MLLL.t00ef6f00 renaming h53 → _p2mH53
open _root_.P2MLLL.t00ef6f00 renaming h54 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn
open _root_.P2MLLL.t00ef6f00 renaming h54 → _p2mH54
open _root_.P2MLLL.t00ef6f00 renaming h55 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn_above
open _root_.P2MLLL.t00ef6f00 renaming h55 → _p2mH55
open _root_.P2MLLL.t00ef6f00 renaming h56 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn_below
open _root_.P2MLLL.t00ef6f00 renaming h56 → _p2mH56
open _root_.P2MLLL.t00ef6f00 renaming h57 → Hex.GramSchmidt.Int.getArrayEntry_writeScaledColumn_diag
open _root_.P2MLLL.t00ef6f00 renaming h57 → _p2mH57
open _root_.P2MLLL.t00ef6f00 renaming h58 → Hex.GramSchmidt.Int.getArrayEntry_zeroRows
open _root_.P2MLLL.t00ef6f00 renaming h58 → _p2mH58
open _root_.P2MLLL.t00ef6f00 renaming h59 → Hex.GramSchmidt.Int.getElem!_foldl_modify_of_mem_nodup
open _root_.P2MLLL.t00ef6f00 renaming h59 → _p2mH59
open _root_.P2MLLL.t00ef6f00 renaming h60 → Hex.GramSchmidt.Int.getElem!_foldl_modify_of_notMem
open _root_.P2MLLL.t00ef6f00 renaming h60 → _p2mH60
open _root_.P2MLLL.t00ef6f00 renaming h61 → Hex.GramSchmidt.Int.getElem!_foldl_setSelf_of_mem_nodup
open _root_.P2MLLL.t00ef6f00 renaming h61 → _p2mH61
open _root_.P2MLLL.t00ef6f00 renaming h62 → Hex.GramSchmidt.Int.getElem!_foldl_setSelf_of_notMem
open _root_.P2MLLL.t00ef6f00 renaming h62 → _p2mH62
open _root_.P2MLLL.t00ef6f00 renaming h63 → Hex.GramSchmidt.Int.getElem!_modify_ne
open _root_.P2MLLL.t00ef6f00 renaming h63 → _p2mH63
open _root_.P2MLLL.t00ef6f00 renaming h64 → Hex.GramSchmidt.Int.getElem!_modify_self
open _root_.P2MLLL.t00ef6f00 renaming h64 → _p2mH64
open _root_.P2MLLL.t00ef6f00 renaming h65 → Hex.GramSchmidt.Int.gramRows_row_size
open _root_.P2MLLL.t00ef6f00 renaming h65 → _p2mH65
open _root_.P2MLLL.t00ef6f00 renaming h66 → Hex.GramSchmidt.Int.gramRows_size
open _root_.P2MLLL.t00ef6f00 renaming h66 → _p2mH66
open _root_.P2MLLL.t00ef6f00 renaming h67 → Hex.GramSchmidt.Int.modify_eq_set!
open _root_.P2MLLL.t00ef6f00 renaming h67 → _p2mH67
open _root_.P2MLLL.t00ef6f00 renaming h68 → Hex.GramSchmidt.Int.modify_size
open _root_.P2MLLL.t00ef6f00 renaming h68 → _p2mH68
open _root_.P2MLLL.t00ef6f00 renaming h69 → Hex.GramSchmidt.Int.rowsToMatrix_gramRows
open _root_.P2MLLL.t00ef6f00 renaming h69 → _p2mH69
open _root_.P2MLLL.t00ef6f00 renaming h70 → Hex.GramSchmidt.Int.rowsToMatrix_stepScaledRows_eq
open _root_.P2MLLL.t00ef6f00 renaming h70 → _p2mH70
open _root_.P2MLLL.t00ef6f00 renaming h71 → Hex.GramSchmidt.Int.scaledCoeffRowsSchur_size
open _root_.P2MLLL.t00ef6f00 renaming h71 → _p2mH71
open _root_.P2MLLL.t00ef6f00 renaming h72 → Hex.GramSchmidt.Int.schurColumnLoop_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h72 → _p2mH72
open _root_.P2MLLL.t00ef6f00 renaming h73 → Hex.GramSchmidt.Int.schurColumnLoop_size
open _root_.P2MLLL.t00ef6f00 renaming h73 → _p2mH73
open _root_.P2MLLL.t00ef6f00 renaming h74 → Hex.GramSchmidt.Int.schurRowLoop_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h74 → _p2mH74
open _root_.P2MLLL.t00ef6f00 renaming h75 → Hex.GramSchmidt.Int.schurRowLoop_size
open _root_.P2MLLL.t00ef6f00 renaming h75 → _p2mH75
open _root_.P2MLLL.t00ef6f00 renaming h76 → Hex.GramSchmidt.Int.setArrayEntry_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h76 → _p2mH76
open _root_.P2MLLL.t00ef6f00 renaming h77 → Hex.GramSchmidt.Int.setArrayEntry_size
open _root_.P2MLLL.t00ef6f00 renaming h77 → _p2mH77
open _root_.P2MLLL.t00ef6f00 renaming h78 → Hex.GramSchmidt.Int.size_foldl_modify
open _root_.P2MLLL.t00ef6f00 renaming h78 → _p2mH78
open _root_.P2MLLL.t00ef6f00 renaming h79 → Hex.GramSchmidt.Int.size_foldl_setSelf
open _root_.P2MLLL.t00ef6f00 renaming h79 → _p2mH79
open _root_.P2MLLL.t00ef6f00 renaming h80 → Hex.GramSchmidt.Int.stepScaledRows_row_at_trailing
open _root_.P2MLLL.t00ef6f00 renaming h80 → _p2mH80
open _root_.P2MLLL.t00ef6f00 renaming h81 → Hex.GramSchmidt.Int.stepScaledRows_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h81 → _p2mH81
open _root_.P2MLLL.t00ef6f00 renaming h82 → Hex.GramSchmidt.Int.stepScaledRows_size
open _root_.P2MLLL.t00ef6f00 renaming h82 → _p2mH82
open _root_.P2MLLL.t00ef6f00 renaming h83 → Hex.GramSchmidt.Int.writeScaledColumn_rows_size
open _root_.P2MLLL.t00ef6f00 renaming h83 → _p2mH83
open _root_.P2MLLL.t00ef6f00 renaming h84 → Hex.GramSchmidt.Int.writeScaledColumn_size
open _root_.P2MLLL.t00ef6f00 renaming h84 → _p2mH84
open _root_.P2MLLL.t00ef6f00 renaming h85 → Hex.GramSchmidt.Int.zeroRows_row_size
open _root_.P2MLLL.t00ef6f00 renaming h85 → _p2mH85
open _root_.P2MLLL.t00ef6f00 renaming h86 → Hex.GramSchmidt.Int.zeroRows_size
open _root_.P2MLLL.t00ef6f00 renaming h86 → _p2mH86


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
Scaled-coefficient and Gram-determinant surface for `hex-gram-schmidt`.

This module packages the executable scaled Gram-Schmidt output: the `Data`
record bundling the leading Gram determinant vector `d` with the scaled
coefficient matrix `ν`, produced by `data` from a single
`scaledCoeffRowsSchur` pass, and exposed as the public `gramDetVec` and
`scaledCoeffs`. It proves the per-row Schur kernel agrees with the reference
`scaledCoeffRows` formulation (`schurSigma_congr` and the column/boundary
frame lemmas), and develops the Bareiss commutation infrastructure the
determinant correspondence rests on: a `Matrix.stepMatrix` step commutes with
taking a `principalSubmatrix` and with taking a trailing `borderedMinor`
(`principalSubmatrix_stepMatrix_eq`, `borderedMinor_stepMatrix_eq`), the no-pivot
loop stays synchronized across a matrix and its bordered minor
(`noPivotLoop_full_eq_borderedMinor_at_trailing`), it preserves trailing-block
symmetry, and its `step`/`singularStep` bookkeeping is monotone and stable
under prefixing.
-/
namespace Hex
namespace GramSchmidt.Int
set_option maxRecDepth 8192
/-- σ-chain dependency frame lemma. The value of `schurSigma rows i j`
depends only on the diagonal cells `rows[k][k]` for `k < j`, the
row-`i` cells `rows[i][p]` for `p < j`, and the row-`j` cells `rows[j][p]`
for `p < j`. The hypothesis `0 < j` makes both initial reads `rows[i][0]`
and `rows[j][0]` fall under `h_i` and `h_j` at `p = 0`. -/
 theorem _root_.P2MLLL.t00ef6f00.h127
    {rows rows' : Array (Array Int)} {i j : Nat} (hj : 0 < j)
    (h_diag : ∀ k, k < j → getArrayEntry rows k k = getArrayEntry rows' k k)
    (h_i : ∀ p, p < j → getArrayEntry rows i p = getArrayEntry rows' i p)
    (h_j : ∀ p, p < j → getArrayEntry rows j p = getArrayEntry rows' j p) :
    schurSigma rows i j = schurSigma rows' i j := by
  -- Generic foldl congruence under pointwise body equality.
  have foldl_congr :
      ∀ (L : List Nat) (init init' : Int),
        init = init' →
        (∀ p ∈ L, ∀ s : Int,
          Matrix.exactDiv
            (getArrayEntry rows p p * s +
              getArrayEntry rows i p * getArrayEntry rows j p)
            (getArrayEntry rows (p - 1) (p - 1)) =
          Matrix.exactDiv
            (getArrayEntry rows' p p * s +
              getArrayEntry rows' i p * getArrayEntry rows' j p)
            (getArrayEntry rows' (p - 1) (p - 1))) →
        L.foldl
            (fun sigma p =>
              Matrix.exactDiv
                (getArrayEntry rows p p * sigma +
                  getArrayEntry rows i p * getArrayEntry rows j p)
                (getArrayEntry rows (p - 1) (p - 1)))
            init =
          L.foldl
            (fun sigma p =>
              Matrix.exactDiv
                (getArrayEntry rows' p p * sigma +
                  getArrayEntry rows' i p * getArrayEntry rows' j p)
                (getArrayEntry rows' (p - 1) (p - 1)))
            init' := by
    intro L
    induction L with
    | nil => intro init init' hinit _; simpa using hinit
    | cons p L ih =>
        intro init init' hinit hstep
        simp only [List.foldl_cons]
        apply ih
        · rw [hinit, hstep p (List.mem_cons_self) init']
        · intro q hq s
          exact hstep q (List.mem_cons_of_mem _ hq) s
  -- Initial accumulator equality at `p = 0`.
  have h_init : getArrayEntry rows i 0 * getArrayEntry rows j 0 =
      getArrayEntry rows' i 0 * getArrayEntry rows' j 0 := by
    rw [h_i 0 hj, h_j 0 hj]
  -- Per-step equality, using `p < j` for every `p` in `[1, j)`.
  have h_step :
      ∀ p ∈ List.range' 1 (j - 1), ∀ s : Int,
        Matrix.exactDiv
          (getArrayEntry rows p p * s +
            getArrayEntry rows i p * getArrayEntry rows j p)
          (getArrayEntry rows (p - 1) (p - 1)) =
        Matrix.exactDiv
          (getArrayEntry rows' p p * s +
            getArrayEntry rows' i p * getArrayEntry rows' j p)
          (getArrayEntry rows' (p - 1) (p - 1)) := by
    intro p hp s
    rw [List.mem_range'] at hp
    have hp_lt : p < j := by omega
    have hp_pred_lt : p - 1 < j := by omega
    rw [h_diag p hp_lt, h_i p hp_lt, h_j p hp_lt, h_diag (p - 1) hp_pred_lt]
  -- Reduce `schurSigma` to a foldl on each side.
  show
    (Id.run do
      let mut sigma := getArrayEntry rows i 0 * getArrayEntry rows j 0
      for p in [1:j] do
        sigma :=
          Matrix.exactDiv
            (getArrayEntry rows p p * sigma +
              getArrayEntry rows i p * getArrayEntry rows j p)
            (getArrayEntry rows (p - 1) (p - 1))
      return sigma) =
    (Id.run do
      let mut sigma := getArrayEntry rows' i 0 * getArrayEntry rows' j 0
      for p in [1:j] do
        sigma :=
          Matrix.exactDiv
            (getArrayEntry rows' p p * sigma +
              getArrayEntry rows' i p * getArrayEntry rows' j p)
            (getArrayEntry rows' (p - 1) (p - 1))
      return sigma)
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  exact foldl_congr _ _ _ h_init h_step
open _root_.P2MLLL.t00ef6f00 renaming h127 → Hex.GramSchmidt.Int.schurSigma_congr
open _root_.P2MLLL.t00ef6f00 renaming h127 → _p2mH127


set_option maxRecDepth 8192
/-- `j = 0` boundary frame lemma. After the full Schur kernel runs, the
`(i, 0)` cell holds the gram entry `gram[i][0]`. This is used by the σ-chain
recurrence (`σ₀ = rows[i][0] · rows[j][0]`) when filling in cells at column
`j > 0`. -/
 theorem _root_.P2MLLL.t00ef6f00.h121
    (b : Matrix Int n m) (i : Nat) :
    getArrayEntry (scaledCoeffRowsSchur b) i 0 =
      getArrayEntry (gramRows b) i 0 := by
  by_cases hin : i < n
  · -- In bounds. The outer row loop hits row `i`, the inner column loop
    -- writes `gram[i][0]` at `(i, 0)`, and later row iterations leave it
    -- alone.
    have h_mem : i ∈ List.range' 0 n := by
      rw [List.mem_range']
      exact ⟨i, by simpa using hin, by simp⟩
    have h_row : i < (zeroRows n).size := by
      rw [_root_.P2MLLL.t00ef6f00.h86]; exact hin
    have h_col : 0 < (zeroRows n)[i]!.size := by
      rw [_root_.P2MLLL.t00ef6f00.h85 n i hin]
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) hin
    simp [scaledCoeffRowsSchur]
    exact _root_.P2MLLL.t00ef6f00.h43 (List.range' 0 n) (zeroRows n)
      (gramRows b) i h_mem h_row h_col
  · -- Out of bounds. The row loop never visits row `i`, so `(i, 0)` stays at
    -- its zero initial value, which matches `gramRows b` out of bounds.
    have hin' : n ≤ i := Nat.le_of_not_lt hin
    have h_not_mem : i ∉ List.range' 0 n := by
      rw [List.mem_range']
      rintro ⟨k, hk, hki⟩
      simp at hki
      omega
    have h_gram_zero : getArrayEntry (gramRows b) i 0 = 0 := by
      have h_gram_size : (gramRows b).size = n := _root_.P2MLLL.t00ef6f00.h66 b
      have h_size_le : (gramRows b).size ≤ i := h_gram_size.symm ▸ hin'
      have h_entry_default : (gramRows b)[i]! = (default : Array Int) := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none h_size_le, Option.getD_none]
      unfold getArrayEntry
      rw [h_entry_default]
      exact _root_.P2MLLL.t00ef6f00.h28 0
    rw [h_gram_zero]
    simp [scaledCoeffRowsSchur]
    rw [_root_.P2MLLL.t00ef6f00.h44 (List.range' 0 n) (zeroRows n)
      (gramRows b) i 0 h_not_mem]
    exact _root_.P2MLLL.t00ef6f00.h58 n i 0
open _root_.P2MLLL.t00ef6f00 renaming h121 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h121 → _p2mH121


set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t00ef6f00.h122
    {n m : Nat} (b : Matrix Int n m) (a c : Nat)
    (h_c_le_a : c ≤ a) (han : a < n) :
    getArrayEntry (scaledCoeffRowsSchur b) a c =
      schurScaledCoeffEntry (scaledCoeffRowsSchur b) (gramRows b) a c := by
  let gram := gramRows b
  let rowPrefix := List.range' 0 a
  let rowSuffix := List.range' (a + 1) (n - (a + 1))
  let rowsBeforeA :=
    rowPrefix.foldl
      (fun next row =>
        (List.range' 0 (row + 1)).foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
          next) (zeroRows n)
  let colPrefix := List.range' 0 c
  let colSuffix := List.range' (c + 1) (a - c)
  let rowsBeforeC :=
    colPrefix.foldl
      (fun next col =>
        setArrayEntry next a col (schurScaledCoeffEntry next gram a col)) rowsBeforeA
  let rowsAfterC :=
    setArrayEntry rowsBeforeC a c (schurScaledCoeffEntry rowsBeforeC gram a c)
  have h_rows_split :
      List.range' 0 n = rowPrefix ++ a :: rowSuffix := by
    dsimp [rowPrefix, rowSuffix]
    have hn_split : n = a + (n - a) := by omega
    have hn_tail : n - a = (n - (a + 1)) + 1 := by omega
    calc
      List.range' 0 n = List.range' 0 (a + (n - a)) := by
        exact congrArg (List.range' 0) hn_split
      _ = List.range' 0 a ++ List.range' a (n - a) := by
        simpa using (List.range'_append_1 (s := 0) (m := a) (n := n - a)).symm
      _ = List.range' 0 a ++ List.range' a ((n - (a + 1)) + 1) := by
        rw [hn_tail]
      _ = List.range' 0 a ++ a :: List.range' (a + 1) (n - (a + 1)) := by
        rw [List.range'_succ]
  have h_cols_split :
      List.range' 0 (a + 1) = colPrefix ++ c :: colSuffix := by
    dsimp [colPrefix, colSuffix]
    have hc_split : a + 1 = c + ((a + 1) - c) := by omega
    have hc_tail : (a + 1) - c = (a - c) + 1 := by omega
    calc
      List.range' 0 (a + 1) = List.range' 0 (c + ((a + 1) - c)) := by
        exact congrArg (List.range' 0) hc_split
      _ = List.range' 0 c ++ List.range' c ((a + 1) - c) := by
        simpa using (List.range'_append_1 (s := 0) (m := c) (n := (a + 1) - c)).symm
      _ = List.range' 0 c ++ List.range' c ((a - c) + 1) := by
        rw [hc_tail]
      _ = List.range' 0 c ++ c :: List.range' (c + 1) (a - c) := by
        rw [List.range'_succ]
  have h_a_not_suffix : a ∉ rowSuffix := by
    dsimp [rowSuffix]
    intro hmem
    rw [List.mem_range'] at hmem
    omega
  have h_c_not_colSuffix : c ∉ colSuffix := by
    dsimp [colSuffix]
    intro hmem
    rw [List.mem_range'] at hmem
    omega
  have hrow_beforeC : a < rowsBeforeC.size := by
    dsimp [rowsBeforeC, rowsBeforeA]
    rw [_root_.P2MLLL.t00ef6f00.h73, _root_.P2MLLL.t00ef6f00.h75, _root_.P2MLLL.t00ef6f00.h86]
    exact han
  have hcol_beforeC : c < rowsBeforeC[a]!.size := by
    dsimp [rowsBeforeC, rowsBeforeA]
    rw [_root_.P2MLLL.t00ef6f00.h72, _root_.P2MLLL.t00ef6f00.h74, _root_.P2MLLL.t00ef6f00.h85 n a han]
    exact Nat.lt_of_le_of_lt h_c_le_a han
  have h_write :
      getArrayEntry (scaledCoeffRowsSchur b) a c =
        schurScaledCoeffEntry rowsBeforeC gram a c := by
    simp [scaledCoeffRowsSchur, gram, h_rows_split, h_cols_split, rowsBeforeA,
      rowsBeforeC]
    rw [_root_.P2MLLL.t00ef6f00.h44 _ _ _ _ _ h_a_not_suffix,
      _root_.P2MLLL.t00ef6f00.h38 _ _ _ _ _ h_c_not_colSuffix]
    exact _root_.P2MLLL.t00ef6f00.h48 rowsBeforeC a c
      (schurScaledCoeffEntry rowsBeforeC gram a c) hrow_beforeC hcol_beforeC
  rw [h_write]
  by_cases hc0 : c = 0
  · simp [schurScaledCoeffEntry, hc0, gram]
  · have hcp : 0 < c := Nat.pos_of_ne_zero hc0
    have h_entry_congr :
        schurScaledCoeffEntry rowsBeforeC gram a c =
          schurScaledCoeffEntry (scaledCoeffRowsSchur b) gram a c := by
      simp [schurScaledCoeffEntry, hc0]
      have h_diag_cells :
          ∀ k, k < c →
            getArrayEntry rowsBeforeC k k =
              getArrayEntry (scaledCoeffRowsSchur b) k k := by
        intro k hk
        have hka : k < a := by omega
        have hk_not_a : k ≠ a := by omega
        have hk_not_suffix : k ∉ rowSuffix := by
          dsimp [rowSuffix]
          intro hmem
          rw [List.mem_range'] at hmem
          omega
        calc
          getArrayEntry rowsBeforeC k k =
              getArrayEntry rowsBeforeA k k := by
            dsimp [rowsBeforeC]
            exact _root_.P2MLLL.t00ef6f00.h41 _ _ _ _ _ _ hk_not_a
          _ = getArrayEntry
              ((List.range' 0 n).foldl
                (fun next row =>
                  (List.range' 0 (row + 1)).foldl
                    (fun next col =>
                      setArrayEntry next row col
                        (schurScaledCoeffEntry next (gramRows b) row col))
                    next) (zeroRows n)) k k := by
            rw [h_rows_split]
            simp [rowsBeforeA, gram]
            rw [_root_.P2MLLL.t00ef6f00.h44 _ _ _ _ _ hk_not_suffix,
              _root_.P2MLLL.t00ef6f00.h41 _ _ _ _ _ _ hk_not_a]
          _ = getArrayEntry (scaledCoeffRowsSchur b) k k := by
            simp [scaledCoeffRowsSchur]
      have h_row_a_cells :
          ∀ p, p < c →
            getArrayEntry rowsBeforeC a p =
              getArrayEntry (scaledCoeffRowsSchur b) a p := by
        intro p hp
        have hp_not_c : p ∉ colSuffix := by
          dsimp [colSuffix]
          intro hmem
          rw [List.mem_range'] at hmem
          omega
        calc
          getArrayEntry rowsBeforeC a p =
              getArrayEntry rowsAfterC a p := by
            dsimp [rowsAfterC]
            rw [_root_.P2MLLL.t00ef6f00.h46]
            omega
          _ = getArrayEntry
              ((colPrefix ++ c :: colSuffix).foldl
                (fun next col =>
                  setArrayEntry next a col (schurScaledCoeffEntry next gram a col))
                rowsBeforeA) a p := by
            simp [colPrefix, rowsBeforeC, rowsAfterC]
            rw [_root_.P2MLLL.t00ef6f00.h38 _ _ _ _ _ hp_not_c]
          _ = getArrayEntry (scaledCoeffRowsSchur b) a p := by
            simp [scaledCoeffRowsSchur, gram, h_rows_split, h_cols_split, rowsBeforeA]
            rw [_root_.P2MLLL.t00ef6f00.h44 _ _ _ _ _ h_a_not_suffix]
      have h_row_c_cells :
          ∀ p, p < c →
            getArrayEntry rowsBeforeC c p =
              getArrayEntry (scaledCoeffRowsSchur b) c p := by
        intro p hp
        by_cases hca : c = a
        · subst a
          have hp_not_c : p ∉ colSuffix := by
            dsimp [colSuffix]
            intro hmem
            rw [List.mem_range'] at hmem
            omega
          calc
            getArrayEntry rowsBeforeC c p =
                getArrayEntry rowsAfterC c p := by
              dsimp [rowsAfterC]
              rw [_root_.P2MLLL.t00ef6f00.h46]
              omega
            _ = getArrayEntry
                ((colPrefix ++ c :: colSuffix).foldl
                  (fun next col =>
                    setArrayEntry next c col (schurScaledCoeffEntry next gram c col))
                  rowsBeforeA) c p := by
              simp [colPrefix, rowsBeforeC, rowsAfterC]
              rw [_root_.P2MLLL.t00ef6f00.h38 _ _ _ _ _ hp_not_c]
            _ = getArrayEntry (scaledCoeffRowsSchur b) c p := by
              simp [scaledCoeffRowsSchur, gram, h_rows_split, h_cols_split, rowsBeforeA]
              rw [_root_.P2MLLL.t00ef6f00.h44 _ _ _ _ _ h_a_not_suffix]
        · have hca_lt : c < a := by omega
          have hca_ne : c ≠ a := by omega
          have hc_not_suffix : c ∉ rowSuffix := by
            dsimp [rowSuffix]
            intro hmem
            rw [List.mem_range'] at hmem
            omega
          calc
            getArrayEntry rowsBeforeC c p =
                getArrayEntry rowsBeforeA c p := by
              dsimp [rowsBeforeC]
              exact _root_.P2MLLL.t00ef6f00.h41 _ _ _ _ _ _ hca_ne
            _ = getArrayEntry
                ((List.range' 0 n).foldl
                  (fun next row =>
                    (List.range' 0 (row + 1)).foldl
                      (fun next col =>
                        setArrayEntry next row col
                          (schurScaledCoeffEntry next (gramRows b) row col))
                      next) (zeroRows n)) c p := by
              rw [h_rows_split]
              simp [rowsBeforeA, gram]
              rw [_root_.P2MLLL.t00ef6f00.h44 _ _ _ _ _ hc_not_suffix,
                _root_.P2MLLL.t00ef6f00.h41 _ _ _ _ _ _ hca_ne]
            _ = getArrayEntry (scaledCoeffRowsSchur b) c p := by
              simp [scaledCoeffRowsSchur]
      have h_diag_prev :
          getArrayEntry rowsBeforeC (c - 1) (c - 1) =
            getArrayEntry (scaledCoeffRowsSchur b) (c - 1) (c - 1) := by
        exact h_diag_cells (c - 1) (by omega)
      have h_sigma :
          schurSigma rowsBeforeC a c =
            schurSigma (scaledCoeffRowsSchur b) a c :=
        _root_.P2MLLL.t00ef6f00.h127 hcp h_diag_cells h_row_a_cells h_row_c_cells
      rw [h_diag_prev, h_sigma]
    exact h_entry_congr
open _root_.P2MLLL.t00ef6f00 renaming h122 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_schurScaledCoeffEntry
open _root_.P2MLLL.t00ef6f00 renaming h122 → _p2mH122




































set_option maxRecDepth 8192
/-- Trailing-block symmetry is preserved by the no-pivot Bareiss loop: if the
input state's matrix is symmetric at indices at or beyond `state.step`, then the
resulting state's matrix is symmetric at indices at or beyond its `step`. The
abstract version takes only the input symmetry hypothesis; the diagonal Bareiss
update commutes through symmetry because the trailing block remains symmetric
after each `stepMatrix` application. -/
 theorem _root_.P2MLLL.t00ef6f00.h123
    {n : Nat} (fuel : Nat) :
    ∀ (state : Matrix.BareissState Int n),
      (∀ a b : Fin n, state.step ≤ a.val → state.step ≤ b.val →
        state.matrix[a][b] = state.matrix[b][a]) →
      ∀ (a b : Fin n),
        (Matrix.noPivotLoop fuel state).step ≤ a.val →
        (Matrix.noPivotLoop fuel state).step ≤ b.val →
        (Matrix.noPivotLoop fuel state).matrix[a][b] =
          (Matrix.noPivotLoop fuel state).matrix[b][a] := by
  induction fuel with
  | zero =>
      intros state h_sym a b ha hb
      change state.matrix[a][b] = state.matrix[b][a]
      change state.step ≤ a.val at ha
      change state.step ≤ b.val at hb
      exact h_sym a b ha hb
  | succ f ih =>
      intros state h_sym a b ha hb
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · -- Singular branch: result is `{state with singularStep := some state.step}`.
          rw [Matrix.noPivotLoop_of_singular f state hDone hp] at ha hb ⊢
          change state.matrix[a][b] = state.matrix[b][a]
          change state.step ≤ a.val at ha
          change state.step ≤ b.val at hb
          exact h_sym a b ha hb
        · -- Regular branch: recurse on the updated state with step + 1.
          rw [Matrix.noPivotLoop_of_regular f state hDone hp] at ha hb ⊢
          let kFin : Fin n := ⟨state.step, Nat.lt_of_succ_lt hDone⟩
          have h_sym_new : ∀ (a' b' : Fin n),
              state.step + 1 ≤ a'.val → state.step + 1 ≤ b'.val →
              (Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot)[a'][b']
                = (Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot)[b'][a'] := by
            intros a' b' ha' hb'
            have ha'_lt : state.step < a'.val := ha'
            have hb'_lt : state.step < b'.val := hb'
            rw [Matrix.stepMatrix_update_eq state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot a' b' ha'_lt hb'_lt]
            rw [Matrix.stepMatrix_update_eq state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot b' a' hb'_lt ha'_lt]
            -- Both sides reduce to `exactDiv` of similar expressions. Identify
            -- the two `Fin n` indices at value `state.step` and use the
            -- trailing-block symmetry of `state.matrix`.
            have h_ab : state.matrix[a'][b'] = state.matrix[b'][a'] :=
              h_sym a' b' (Nat.le_of_lt ha'_lt) (Nat.le_of_lt hb'_lt)
            have h_ak : state.matrix[a'][kFin] = state.matrix[kFin][a'] :=
              h_sym a' kFin (Nat.le_of_lt ha'_lt) (Nat.le_refl _)
            have h_bk : state.matrix[b'][kFin] = state.matrix[kFin][b'] :=
              h_sym b' kFin (Nat.le_of_lt hb'_lt) (Nat.le_refl _)
            -- The two `Fin n` indices in the unfolded `stepMatrix_update_eq`
            -- have value `state.step` and so equal `kFin` definitionally.
            change Matrix.exactDiv (_ * state.matrix[a'][b']
                - state.matrix[a'][kFin] * state.matrix[kFin][b']) _
              = Matrix.exactDiv (_ * state.matrix[b'][a']
                - state.matrix[b'][kFin] * state.matrix[kFin][a']) _
            rw [h_ab, h_ak, h_bk]
            congr 1
            grind
          exact ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            (by
              intros a' b' ha' hb'
              exact h_sym_new a' b' ha' hb')
            a b ha hb
      · -- Boundary case: `noPivotLoop` returns the input state unchanged.
        rw [Matrix.noPivotLoop_done f state hDone] at ha hb ⊢
        change state.matrix[a][b] = state.matrix[b][a]
        change state.step ≤ a.val at ha
        change state.step ≤ b.val at hb
        exact h_sym a b ha hb
open _root_.P2MLLL.t00ef6f00 renaming h123 → Hex.GramSchmidt.Int.noPivotLoop_matrix_symm_preserve
open _root_.P2MLLL.t00ef6f00 renaming h123 → _p2mH123














set_option maxRecDepth 8192
/-- When the no-pivot Bareiss loop starts from a non-singular state and records
a singular step within `fuel` iterations, the recorded singular index is
strictly bounded by the initial step plus the fuel. The singular branch sets
`singularStep := some state.step` at the trigger iteration, and `state.step`
advances by at most one per regular iteration; with `fuel` iterations available
and at least one used for the singular trigger, the recorded index is `< start
+ fuel`. -/
theorem _root_.P2MLLL.t00ef6f00.h2
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState Int n)
    (h_init : state.singularStep = none)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop fuel state).singularStep = some s) :
    s < state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      rw [Matrix.noPivotLoop_zero_fuel, h_init] at h_sing
      nomatch h_sing
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_of_singular f state hDone hp] at h_sing
          simp at h_sing
          omega
        · rw [Matrix.noPivotLoop_of_regular f state hDone hp] at h_sing
          have h_ih := ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            rfl h_sing
          change s < state.step + 1 + f at h_ih
          show s < state.step + (f + 1)
          omega
      · rw [Matrix.noPivotLoop_done f state hDone] at h_sing
        rw [h_init] at h_sing
        nomatch h_sing
open _root_.P2MLLL.t00ef6f00 renaming h2 → Hex.GramSchmidt.Int.noPivotLoop_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h2 → _p2mH2


set_option maxRecDepth 8192
/-- After running `fuel` iterations of `Matrix.noPivotLoop` from a state with
no recorded singular step, if the result also has no recorded singular step
and the loop had at least `fuel + 1` steps of room from its starting step,
then the result's step is the starting step plus `fuel`. -/
 theorem _root_.P2MLLL.t00ef6f00.h126
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState Int n)
    (h_init : state.singularStep = none)
    (h_room : state.step + fuel + 1 ≤ n)
    (h_no_sing : (Matrix.noPivotLoop fuel state).singularStep = none) :
    (Matrix.noPivotLoop fuel state).step = state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step = state.step + 0
      omega
  | succ f ih =>
      have hDone : state.step + 1 < n := by omega
      by_cases hp : state.matrix[state.step][state.step] = 0
      · rw [Matrix.noPivotLoop_of_singular f state hDone hp] at h_no_sing
        simp at h_no_sing
      · rw [Matrix.noPivotLoop_of_regular f state hDone hp] at h_no_sing
        rw [Matrix.noPivotLoop_of_regular f state hDone hp]
        have h_next_room : state.step + 1 + f + 1 ≤ n := by omega
        have h_next_step := ih
          { step := state.step + 1
            matrix := Matrix.stepMatrix state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          rfl h_next_room h_no_sing
        rw [h_next_step]
        show state.step + 1 + f = state.step + (f + 1)
        omega
open _root_.P2MLLL.t00ef6f00 renaming h126 → Hex.GramSchmidt.Int.noPivotLoop_step_eq_add_of_singularStep_none
open _root_.P2MLLL.t00ef6f00 renaming h126 → _p2mH126




set_option maxRecDepth 8192
/-- The `step` field of a no-pivot Bareiss state never decreases under further
loop iterations. -/
theorem _root_.P2MLLL.t00ef6f00.h3
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState Int n) :
    state.step ≤ (Matrix.noPivotLoop fuel state).step := by
  induction fuel generalizing state with
  | zero =>
      show state.step ≤ state.step
      omega
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · have hStepLt : state.step < n := Nat.lt_of_succ_lt hDone
        by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_of_singular f state hDone hp]
          show state.step ≤ state.step
          omega
        · rw [Matrix.noPivotLoop_of_regular f state hDone hp]
          have h_ih := ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          -- h_ih says state.step + 1 ≤ (noPivotLoop f next).step
          -- Want: state.step ≤ (noPivotLoop f next).step
          exact Nat.le_trans (Nat.le_succ _) h_ih
      · rw [Matrix.noPivotLoop_done f state hDone]
        show state.step ≤ state.step
        omega
open _root_.P2MLLL.t00ef6f00 renaming h3 → Hex.GramSchmidt.Int.noPivotLoop_step_monotone
open _root_.P2MLLL.t00ef6f00 renaming h3 → _p2mH3


set_option maxRecDepth 8192
/-- A singular step recorded by an initial no-pivot prefix remains the recorded
singular step after any further no-pivot iterations. -/
 theorem _root_.P2MLLL.t00ef6f00.h125
    {n : Nat} (a b : Nat) (state : Matrix.BareissState Int n)
    (h_init : state.singularStep = none) {s : Nat}
    (h_prefix : (Matrix.noPivotLoop a state).singularStep = some s) :
    (Matrix.noPivotLoop (a + b) state).singularStep = some s := by
  rw [noPivotLoop_add a b state]
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, h_step, h_zero, h_bound⟩
  · rw [h_none] at h_prefix
    nomatch h_prefix
  · have hs : s = k.val := by
      rw [h_sing] at h_prefix
      injection h_prefix with h
      exact h.symm
    have hDone :
        (Matrix.noPivotLoop a state).step + 1 < n := by
      rw [h_step]
      exact h_bound
    have hidx :
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step
    have hp :
        (Matrix.noPivotLoop a state).matrix[
            (⟨(Matrix.noPivotLoop a state).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)][
            (⟨(Matrix.noPivotLoop a state).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
      have h_lift := congrArg
        (fun (idx : Fin n) => (Matrix.noPivotLoop a state).matrix[idx][idx])
        hidx
      exact h_lift.trans h_zero
    have hsing_state :
        (Matrix.noPivotLoop a state).singularStep =
          some (Matrix.noPivotLoop a state).step := by
      rw [h_sing, h_step]
    rw [noPivotLoop_id_at_singular_fixedpoint b _ hDone hp hsing_state, hs]
    exact h_sing
open _root_.P2MLLL.t00ef6f00 renaming h125 → Hex.GramSchmidt.Int.noPivotLoop_singularStep
open _root_.P2MLLL.t00ef6f00 renaming h125 → _p2mH125


set_option maxRecDepth 8192
/-- If a full no-pivot run has no singular step, every initial prefix run also
has no singular step. -/
 theorem _root_.P2MLLL.t00ef6f00.h124
    {n : Nat} (a b : Nat) (state : Matrix.BareissState Int n)
    (h_init : state.singularStep = none)
    (h_final : (Matrix.noPivotLoop (a + b) state).singularStep = none) :
    (Matrix.noPivotLoop a state).singularStep = none := by
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, _h_step, _h_zero, _h_bound⟩
  · exact h_none
  · have h_persist :=
      _root_.P2MLLL.t00ef6f00.h125 a b state h_init h_sing
    rw [h_final] at h_persist
    nomatch h_persist
open _root_.P2MLLL.t00ef6f00 renaming h124 → Hex.GramSchmidt.Int.noPivotLoop_prefix_none_of_final_none
open _root_.P2MLLL.t00ef6f00 renaming h124 → _p2mH124








end GramSchmidt.Int
open _root_.P2MLLL.t00ef6f00 renaming h2 → Hex.GramSchmidt.Int.noPivotLoop_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h2 → _p2mH2
open _root_.P2MLLL.t00ef6f00 renaming h3 → Hex.GramSchmidt.Int.noPivotLoop_step_monotone
open _root_.P2MLLL.t00ef6f00 renaming h3 → _p2mH3
open _root_.P2MLLL.t00ef6f00 renaming h121 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h121 → _p2mH121
open _root_.P2MLLL.t00ef6f00 renaming h122 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_schurScaledCoeffEntry
open _root_.P2MLLL.t00ef6f00 renaming h122 → _p2mH122
open _root_.P2MLLL.t00ef6f00 renaming h123 → Hex.GramSchmidt.Int.noPivotLoop_matrix_symm_preserve
open _root_.P2MLLL.t00ef6f00 renaming h123 → _p2mH123
open _root_.P2MLLL.t00ef6f00 renaming h124 → Hex.GramSchmidt.Int.noPivotLoop_prefix_none_of_final_none
open _root_.P2MLLL.t00ef6f00 renaming h124 → _p2mH124
open _root_.P2MLLL.t00ef6f00 renaming h125 → Hex.GramSchmidt.Int.noPivotLoop_singularStep
open _root_.P2MLLL.t00ef6f00 renaming h125 → _p2mH125
open _root_.P2MLLL.t00ef6f00 renaming h126 → Hex.GramSchmidt.Int.noPivotLoop_step_eq_add_of_singularStep_none
open _root_.P2MLLL.t00ef6f00 renaming h126 → _p2mH126
open _root_.P2MLLL.t00ef6f00 renaming h127 → Hex.GramSchmidt.Int.schurSigma_congr
open _root_.P2MLLL.t00ef6f00 renaming h127 → _p2mH127

end Hex
open _root_.P2MLLL.t00ef6f00 renaming h2 → Hex.GramSchmidt.Int.noPivotLoop_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h2 → _p2mH2
open _root_.P2MLLL.t00ef6f00 renaming h3 → Hex.GramSchmidt.Int.noPivotLoop_step_monotone
open _root_.P2MLLL.t00ef6f00 renaming h3 → _p2mH3
open _root_.P2MLLL.t00ef6f00 renaming h121 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h121 → _p2mH121
open _root_.P2MLLL.t00ef6f00 renaming h122 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_schurScaledCoeffEntry
open _root_.P2MLLL.t00ef6f00 renaming h122 → _p2mH122
open _root_.P2MLLL.t00ef6f00 renaming h123 → Hex.GramSchmidt.Int.noPivotLoop_matrix_symm_preserve
open _root_.P2MLLL.t00ef6f00 renaming h123 → _p2mH123
open _root_.P2MLLL.t00ef6f00 renaming h124 → Hex.GramSchmidt.Int.noPivotLoop_prefix_none_of_final_none
open _root_.P2MLLL.t00ef6f00 renaming h124 → _p2mH124
open _root_.P2MLLL.t00ef6f00 renaming h125 → Hex.GramSchmidt.Int.noPivotLoop_singularStep
open _root_.P2MLLL.t00ef6f00 renaming h125 → _p2mH125
open _root_.P2MLLL.t00ef6f00 renaming h126 → Hex.GramSchmidt.Int.noPivotLoop_step_eq_add_of_singularStep_none
open _root_.P2MLLL.t00ef6f00 renaming h126 → _p2mH126
open _root_.P2MLLL.t00ef6f00 renaming h127 → Hex.GramSchmidt.Int.schurSigma_congr
open _root_.P2MLLL.t00ef6f00 renaming h127 → _p2mH127


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t00ef6f00 renaming h2 → Hex.GramSchmidt.Int.noPivotLoop_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h2 → _p2mH2
open _root_.P2MLLL.t00ef6f00 renaming h3 → Hex.GramSchmidt.Int.noPivotLoop_step_monotone
open _root_.P2MLLL.t00ef6f00 renaming h3 → _p2mH3

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



section



set_option autoImplicit true



section

namespace Hex
namespace GramSchmidt.Int
/-! # Gram row-span invariant for no-pivot Bareiss -/









































/-! # Canonical coefficient vector and canonicity predicate -/



























set_option maxRecDepth 8192
/-- If the initial no-pivot Gram pass reaches column `s` without recording a
singular step, its state step is exactly `s`.  This keeps the later singular
pivot argument from unfolding the loop just to align the searched column. -/
 theorem _root_.P2MLLL.t00ef6f00.h12
    (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.noPivotLoop s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step = s := by
  have h_room :
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + s + 1 ≤ n := by
    simp [Matrix.noPivotInitialState]
    omega
  have h_step :=
    Matrix.noPivotLoop_step_eq_add_of_singularStep_none s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_room h_prefix_none
  simpa [Matrix.noPivotInitialState] using h_step
open _root_.P2MLLL.t00ef6f00 renaming h12 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_step_eq
open _root_.P2MLLL.t00ef6f00 renaming h12 → _p2mH12




















end GramSchmidt.Int
open _root_.P2MLLL.t00ef6f00 renaming h12 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_step_eq
open _root_.P2MLLL.t00ef6f00 renaming h12 → _p2mH12

end Hex
open _root_.P2MLLL.t00ef6f00 renaming h12 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_step_eq
open _root_.P2MLLL.t00ef6f00 renaming h12 → _p2mH12


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
Bareiss row-invariant proofs for the no-pivot Gram pass in `hex-gram-schmidt`.

This module establishes that the no-pivot Bareiss elimination over a Gram
matrix carries the `BareissGramRowInvariant` row-coefficient invariant and
that its coefficients stay canonical (matching `bareissGramCanonicalCoeff`),
threading the `StepWitness`/`IsCanonicalAt` quotient gate through the
recursion. It proves the supporting fraction-free divisibility and
singular-step facts (exact divisibility of each Bareiss step, propagation of
the first singular step, and that a singular leading Gram prefix forces the
later leading determinants to zero), the integer dot-product degeneracy
lemmas, and the row-combination expansion of inner products. It also supplies
the `scaledCoeffArrayLoop` branch/size lemmas (singular, regular, last-step,
done, and current-column-written) that the correspondence proofs unfold.
-/
namespace Hex
namespace GramSchmidt.Int




set_option maxRecDepth 8192
/-- The produced row invariant from the initial no-pivot Gram trajectory is
canonical: its coefficients match `bareissGramCanonicalCoeff` at every fuel
index. This is the canonicity gate consumed by `StepWitness.Cell`. -/
 theorem _root_.P2MLLL.t00ef6f00.h93
    (b : Matrix Int n m) (fuel : Nat) (hquot : StepWitness b) :
    IsCanonicalAt b fuel
      (_root_.Hex.GramSchmidt.Int.bareissGramRowInvariant_noPivotLoop_initial b fuel hquot) := by
  intro i
  have key := (_root_.Hex.GramSchmidt.Int.bareissGramRowInvariant_noPivotLoop_initialAux
    (b := b) 0 fuel (bareissGramRowInvariant_initial b)
    (isCanonicalAt_initial b) rfl hquot).2 i
  simp only [Nat.zero_add] at key
  exact key
open _root_.P2MLLL.t00ef6f00 renaming h93 → Hex.GramSchmidt.Int.bareissGramRowInvariant_noPivotLoop_initial_canonical
open _root_.P2MLLL.t00ef6f00 renaming h93 → _p2mH93


set_option maxRecDepth 8192
/-- Matrix-level Bareiss-step divisibility on the initial no-pivot Gram
trajectory: the numerator of one fraction-free row update is divisible by the
previous pivot. The witness comes from the canonical-`StepWitness` quotient
package applied at the reachable regular step, with the matrix-level numerator
recovered by taking the dot product of the coefficient-level identity against
the input row `b.row j`. -/
 theorem _root_.P2MLLL.t00ef6f00.h111
    (b : Matrix Int n m) (hquot : StepWitness b)
    (fuel : Nat)
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (i j : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) :
    let state := Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))
    let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
    state.prevPivot ∣
      state.matrix[k][k] * state.matrix[i][j] -
        state.matrix[i][k] * state.matrix[k][j] := by
  intro state k
  let hinv := _root_.Hex.GramSchmidt.Int.bareissGramRowInvariant_noPivotLoop_initial b fuel hquot
  let h_canon := _root_.P2MLLL.t00ef6f00.h93 b fuel hquot
  have hq := hquot fuel hinv h_canon h_prefix_none hnext hp i hi
  have h_step_le_i : state.step ≤ i.val := Nat.le_trans (Nat.le_succ _) hi
  have h_step_le_k : state.step ≤ k.val := Nat.le_refl _
  refine ⟨(Matrix.vecMul (Vector.ofFn hq.q) b).dotProduct (b.row j), ?_⟩
  rw [hinv.entry_eq_dot i j h_step_le_i, hinv.entry_eq_dot k j h_step_le_k]
  rw [← _root_.Hex.GramSchmidt.Int.dot_bareiss_row_update_left state.matrix[k][k] state.matrix[i][k]
        (Matrix.vecMul (hinv.coeff i) b)
        (Matrix.vecMul (hinv.coeff k) b)
        (b.row j)]
  rw [← _root_.Hex.GramSchmidt.Int.vecMul_bareiss_coeff_update b
        state.matrix[k][k] state.matrix[i][k] (hinv.coeff i) (hinv.coeff k)]
  have h_q_eq_num :
      (Vector.ofFn fun a : Fin n =>
        state.matrix[k][k] * (hinv.coeff i)[a] -
          state.matrix[i][k] * (hinv.coeff k)[a]) =
        Vector.ofFn fun a : Fin n => hq.q a * state.prevPivot := by
    apply Vector.ext
    intro a ha
    rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
    have hnum := hq.coeff_num_eq_mul ⟨a, ha⟩
    simp only [Matrix.getElem_pair_eq_nested] at hnum
    exact hnum
  rw [h_q_eq_num, _root_.Hex.GramSchmidt.Int.dot_vecMul_mul_right_int b hq.q state.prevPivot (b.row j)]
  exact Int.mul_comm _ _
open _root_.P2MLLL.t00ef6f00 renaming h111 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_bareiss_step_dvd
open _root_.P2MLLL.t00ef6f00 renaming h111 → _p2mH111


set_option maxRecDepth 8192
/-- Row-vector consumer for an initial no-pivot Gram pass.  A single supported
integer row combination represents the active row `i` against every original
input row, so downstream singular-column arguments do not need to inspect
`BareissGramRowInvariant` or supply the generic regular-branch row-entry
equation. -/
 theorem _root_.P2MLLL.t00ef6f00.h112
    (b : Matrix Int n m) (fuel : Nat)
    (hquot : StepWitness b)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ i.val) :
    ∃ v : Vector Int m,
      (∃ c : Vector Int n,
        (∀ k : Fin n, i.val < k.val → c[k] = 0) ∧
          v = Matrix.vecMul c b) ∧
        ∀ j : Fin n,
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] =
            v.dotProduct (b.row j) := by
  let hinv :=
    _root_.Hex.GramSchmidt.Int.bareissGramRowInvariant_noPivotLoop_initial b fuel hquot
  refine ⟨Matrix.vecMul (hinv.coeff i) b, ?_, ?_⟩
  · exact ⟨hinv.coeff i, fun k hik => hinv.coeff_supp i k hi hik, rfl⟩
  · intro j
    exact hinv.entry_eq_dot i j hi
open _root_.P2MLLL.t00ef6f00 renaming h112 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_exists_rowVec
open _root_.P2MLLL.t00ef6f00 renaming h112 → _p2mH112


set_option maxRecDepth 8192
/-- `int_mul_self_nonneg`: the square `x * x` of an integer is nonnegative,
the base nonnegativity fact for the integer-vector self-dot bounds below. -/
 theorem _root_.P2MLLL.t00ef6f00.h108 (x : Int) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using
    (Lean.Grind.OrderedRing.sq_nonneg (a := x))
open _root_.P2MLLL.t00ef6f00 renaming h108 → Hex.GramSchmidt.Int.int_mul_self_nonneg
open _root_.P2MLLL.t00ef6f00 renaming h108 → _p2mH108


set_option maxRecDepth 8192
/-- `int_mul_self_eq_zero_of_nonpos`: an integer whose square is nonpositive is
zero, the per-component step turning a vanishing self-dot into a zero entry. -/
 theorem _root_.P2MLLL.t00ef6f00.h107 (x : Int) (h : x * x ≤ 0) : x = 0 := by
  have hnonneg : 0 ≤ x * x := _root_.P2MLLL.t00ef6f00.h108 x
  have hsquare : x * x = 0 := Int.le_antisymm h hnonneg
  rcases Int.mul_eq_zero.mp hsquare with h0 | h0 <;> exact h0
open _root_.P2MLLL.t00ef6f00 renaming h107 → Hex.GramSchmidt.Int.int_mul_self_eq_zero_of_nonpos
open _root_.P2MLLL.t00ef6f00 renaming h107 → _p2mH107


set_option maxRecDepth 8192
/-- `foldl_int_dot_self_start_le`: the running self-dot fold over `xs` never
drops below its nonnegative starting accumulator, since each added square is
nonnegative; the monotonicity used to pin the accumulator at zero. -/
 theorem _root_.P2MLLL.t00ef6f00.h99 (xs : List (Fin m)) (v : Vector Int m)
    (acc : Int) (hacc : 0 ≤ acc) :
    acc ≤ xs.foldl (fun sum i => sum + v[i] * v[i]) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hsq : 0 ≤ v[i] * v[i] := _root_.P2MLLL.t00ef6f00.h108 v[i]
      have hnext : 0 ≤ acc + v[i] * v[i] := by grind
      exact Int.le_trans (by grind) (ih (acc := acc + v[i] * v[i]) hnext)
open _root_.P2MLLL.t00ef6f00 renaming h99 → Hex.GramSchmidt.Int.foldl_int_dot_self_start_le
open _root_.P2MLLL.t00ef6f00 renaming h99 → _p2mH99


set_option maxRecDepth 8192
/-- `foldl_int_dot_self_eq_zero_of_mem`: if the self-dot fold over `xs` from a
nonnegative accumulator vanishes, then every entry indexed by `xs` is zero,
the per-index extraction behind finite-dimensional positive-definiteness. -/
 theorem _root_.P2MLLL.t00ef6f00.h98 (xs : List (Fin m))
    (v : Vector Int m) (acc : Int) (hacc : 0 ≤ acc)
    (hzero : xs.foldl (fun sum i => sum + v[i] * v[i]) acc = 0) :
    ∀ i ∈ xs, v[i] = 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons head rest ih =>
      intro i hi
      simp only [List.mem_cons] at hi
      have hsq : 0 ≤ v[head] * v[head] := _root_.P2MLLL.t00ef6f00.h108 v[head]
      have hnext_nonneg : 0 ≤ acc + v[head] * v[head] := by grind
      have hnext_le_zero : acc + v[head] * v[head] ≤ 0 := by
        have hle :=
          _root_.P2MLLL.t00ef6f00.h99 (xs := rest) (v := v)
            (acc := acc + v[head] * v[head]) hnext_nonneg
        have hzero' :
            rest.foldl (fun sum i => sum + v[i] * v[i])
              (acc + v[head] * v[head]) = 0 := by
          simpa using hzero
        rw [hzero'] at hle
        exact hle
      have hnext_zero : acc + v[head] * v[head] = 0 := by grind
      have hhead_zero : v[head] = 0 := by
        apply _root_.P2MLLL.t00ef6f00.h107
        grind
      cases hi with
      | inl h =>
          subst i
          exact hhead_zero
      | inr h =>
          exact ih (acc := acc + v[head] * v[head]) hnext_nonneg hzero i h
open _root_.P2MLLL.t00ef6f00 renaming h98 → Hex.GramSchmidt.Int.foldl_int_dot_self_eq_zero_of_mem
open _root_.P2MLLL.t00ef6f00 renaming h98 → _p2mH98


set_option maxRecDepth 8192
/-- From a vanishing self-dot `v.dotProduct v = 0`, each component `v[i]` is
zero, specializing the fold lemma to the full index list. -/
 theorem _root_.P2MLLL.t00ef6f00.h106 (v : Vector Int m)
    (hzero : v.dotProduct v = 0) (i : Fin m) :
    v[i] = 0 := by
  have hmem : i ∈ List.finRange m := by simp
  exact _root_.P2MLLL.t00ef6f00.h98 (xs := List.finRange m) (v := v)
    (acc := 0) (by decide)
    (by simpa [Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using hzero) i hmem
open _root_.P2MLLL.t00ef6f00 renaming h106 → Hex.GramSchmidt.Int.int_dot_self_eq_zero_get
open _root_.P2MLLL.t00ef6f00 renaming h106 → _p2mH106


set_option maxRecDepth 8192
/-- If `v : Vector Int m` has zero self-dot product, then any other integer
vector dots it to zero from the left as well. -/
 theorem _root_.P2MLLL.t00ef6f00.h105 (u v : Vector Int m)
    (hzero : v.dotProduct v = 0) :
    v.dotProduct u = 0 := by
  unfold Vector.dotProduct
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [_root_.P2MLLL.t00ef6f00.h106 v hzero i]
      have hzero_mul : (0 : Int) * u[i] = 0 := by grind
      rw [hzero_mul]
      have hadd_zero : (0 : Int) + 0 = 0 := by grind
      rw [hadd_zero]
      exact ih
open _root_.P2MLLL.t00ef6f00 renaming h105 → Hex.GramSchmidt.Int.int_dot_eq_zero_of_dot_self_zero_left
open _root_.P2MLLL.t00ef6f00 renaming h105 → _p2mH105


set_option maxRecDepth 8192
/-- `foldl_dot_comm_int_local`: folding `u[i] * v[i]` over `xs` equals folding
`v[i] * u[i]` from an equal starting accumulator, the fold-level symmetry
underlying commutativity of the integer dot product. -/
 theorem _root_.P2MLLL.t00ef6f00.h97 {n' : Nat} (xs : List (Fin n'))
    (u v : Vector Int n') (accU accV : Int) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind
open _root_.P2MLLL.t00ef6f00 renaming h97 → Hex.GramSchmidt.Int.foldl_dot_comm_int_local
open _root_.P2MLLL.t00ef6f00 renaming h97 → _p2mH97


set_option maxRecDepth 8192
/-- The dot product of integer vectors is commutative. (Local form for use
inside this file before the existing `dot_comm_int` declaration.) -/
 theorem _root_.P2MLLL.t00ef6f00.h104 {n' : Nat} (u v : Vector Int n') :
    u.dotProduct v = v.dotProduct u := by
  simpa [Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using
    _root_.P2MLLL.t00ef6f00.h97 (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl
open _root_.P2MLLL.t00ef6f00 renaming h104 → Hex.GramSchmidt.Int.int_dot_comm_local
open _root_.P2MLLL.t00ef6f00 renaming h104 → _p2mH104


set_option maxRecDepth 8192
/-- Pointwise function equality for foldl-style sums lifts to a foldl equality. -/
 theorem _root_.P2MLLL.t00ef6f00.h95 {α : Type v}
    (xs : List α) (f g : α → Int) (acc : Int)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y :=
        fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      exact ih (acc + g x) hxs
open _root_.P2MLLL.t00ef6f00 renaming h95 → Hex.GramSchmidt.Int.foldl_add_pointwise_eq_int
open _root_.P2MLLL.t00ef6f00 renaming h95 → _p2mH95


set_option maxRecDepth 8192
/-- Entry-level formula for `vecMul` over integers: the `j`th entry is
the sum over `k` of `b[k][j] * c[k]`. -/
 theorem _root_.P2MLLL.t00ef6f00.h103
    {n m : Nat} (b : Matrix Int n m) (c : Vector Int n) (j : Fin m) :
    (Matrix.vecMul c b)[j] =
      Fin.foldl n (fun acc k => acc + b[k][j] * c[k]) 0 := by
  rw [Fin.foldl_eq_finRange_foldl]
  show (Matrix.transpose b * c)[j] = _
  rw [Matrix.getElem_mulVec]
  unfold Vector.dotProduct
  apply _root_.P2MLLL.t00ef6f00.h95
  intro k _hk
  simp [Matrix.col]
open _root_.P2MLLL.t00ef6f00 renaming h103 → Hex.GramSchmidt.Int.getElem_vecMul_int
open _root_.P2MLLL.t00ef6f00 renaming h103 → _p2mH103


set_option maxRecDepth 8192
/-- Distribute a constant `x : Int` through a foldl-style sum body. -/
 theorem _root_.P2MLLL.t00ef6f00.h100 {α : Type v}
    (xs : List α) (f : α → Int) (x acc : Int) :
    x * xs.foldl (fun acc y => acc + f y) acc =
      xs.foldl (fun acc y => acc + x * f y) (x * acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons y rest ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + f y)]
      have : x * (acc + f y) = x * acc + x * f y := by grind
      rw [this]
open _root_.P2MLLL.t00ef6f00 renaming h100 → Hex.GramSchmidt.Int.foldl_mul_distrib_int
open _root_.P2MLLL.t00ef6f00 renaming h100 → _p2mH100


set_option maxRecDepth 8192
/-- Expansion of the dot product against `vecMul` over integers: the
second argument's row combination distributes outside the sum, giving the
Σ-over-rows form. Proved via the `List.foldl_add_comm` Fubini
identity. -/
 theorem _root_.P2MLLL.t00ef6f00.h94
    {n m : Nat} (b : Matrix Int n m) (u : Vector Int m) (c : Vector Int n) :
    u.dotProduct (Matrix.vecMul c b) =
      Fin.foldl n
        (fun acc k => acc + c[k] * u.dotProduct (b.row k)) 0 := by
  rw [Fin.foldl_eq_finRange_foldl]
  -- Step 1: rewrite each (rowComb b c)[j] entry using getElem_vecMul_int.
  have h_lhs :
      u.dotProduct (Matrix.vecMul c b) =
        (List.finRange m).foldl
          (fun accj j => accj + u[j] *
            (List.finRange n).foldl (fun acck k => acck + b[k][j] * c[k]) 0) 0 := by
    unfold Vector.dotProduct
    apply _root_.P2MLLL.t00ef6f00.h95
    intro j _hj
    rw [_root_.P2MLLL.t00ef6f00.h103 (b := b) (c := c) j, Fin.foldl_eq_finRange_foldl]
  rw [h_lhs]
  -- Step 2: distribute u[j] over the inner sum so the body has shape (acc + f j k).
  have h_distrib :
      (List.finRange m).foldl
          (fun accj j => accj + u[j] *
            (List.finRange n).foldl (fun acck k => acck + b[k][j] * c[k]) 0) 0 =
        (List.finRange m).foldl
          (fun accj j => accj +
            (List.finRange n).foldl
              (fun acck k => acck + u[j] * (b[k][j] * c[k])) 0) 0 := by
    apply _root_.P2MLLL.t00ef6f00.h95
    intro j _hj
    have h_mul := _root_.P2MLLL.t00ef6f00.h100 (List.finRange n)
      (fun k : Fin n => b[k][j] * c[k]) u[j] 0
    have h_zero : u[j] * (0 : Int) = 0 := by grind
    rw [h_zero] at h_mul
    exact h_mul
  rw [h_distrib]
  -- Step 3: apply Fubini sum-swap.
  have h_swap :=
    _root_.P2MLLL.t00ef6f00.h9 (R := Int)
      (xs := List.finRange m) (ys := List.finRange n)
      (fun (j : Fin m) (k : Fin n) => u[j] * (b[k][j] * c[k]))
  rw [h_swap]
  -- Step 4: reshape each inner sum to match c[k] * dot u (b.row k).
  apply _root_.P2MLLL.t00ef6f00.h95
  intro k _hk
  -- We want:
  --   (List.finRange m).foldl (fun accj j => accj + u[j] * (b[k][j] * c[k])) 0
  --     = c[k] * u.dotProduct (b.row k)
  -- Rearrange body so c[k] is the multiplier: u[j] * (b[k][j] * c[k])
  --     = c[k] * (u[j] * b[k][j]).
  have h_body :
      (List.finRange m).foldl
          (fun accj j => accj + u[j] * (b[k][j] * c[k])) 0 =
        (List.finRange m).foldl
          (fun accj j => accj + c[k] * (u[j] * b[k][j])) 0 := by
    apply _root_.P2MLLL.t00ef6f00.h95
    intro j _hj
    have : u[j] * (b[k][j] * c[k]) = c[k] * (u[j] * b[k][j]) := by grind
    exact this
  rw [h_body]
  -- Pull c[k] out of the foldl using foldl_mul_distrib_int (in reverse).
  have h_pull := _root_.P2MLLL.t00ef6f00.h100 (List.finRange m)
    (fun j : Fin m => u[j] * b[k][j]) c[k] 0
  have h_zero : c[k] * (0 : Int) = 0 := by grind
  rw [h_zero] at h_pull
  rw [← h_pull]
  -- Goal: c[k] * (List.finRange m).foldl (fun accj j => accj + u[j] * b[k][j]) 0
  --      = c[k] * u.dotProduct (b.row k)
  -- Rewrite definitionally.dotProduct to the foldl form using row entry equality.
  have h_dot_eq :
      u.dotProduct (b.row k) =
        (List.finRange m).foldl (fun accj j => accj + u[j] * b[k][j]) 0 := by
    unfold Vector.dotProduct
    apply _root_.P2MLLL.t00ef6f00.h95
    intro j _hj
    simp [Matrix.row]
  rw [h_dot_eq]
open _root_.P2MLLL.t00ef6f00 renaming h94 → Hex.GramSchmidt.Int.dot_vecMul_right_eq
open _root_.P2MLLL.t00ef6f00 renaming h94 → _p2mH94


set_option maxRecDepth 8192
/-- A foldl-style sum whose every term is zero starting from a zero accumulator
collapses to zero. -/
 theorem _root_.P2MLLL.t00ef6f00.h96 {α : Type v}
    (xs : List α) (f : α → Int)
    (h : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) (0 : Int) = 0 := by
  have h_aux : ∀ (xs : List α) (acc : Int),
      (∀ x ∈ xs, f x = 0) →
        xs.foldl (fun acc x => acc + f x) acc = acc := by
    intro xs
    induction xs with
    | nil => intros acc _h; rfl
    | cons y rest ih =>
        intros acc h_terms
        simp only [List.foldl_cons]
        have hy : f y = 0 := h_terms y (by simp)
        have hxs : ∀ x ∈ rest, f x = 0 :=
          fun x hx => h_terms x (List.mem_cons_of_mem _ hx)
        rw [hy]
        have h_add : acc + (0 : Int) = acc := by grind
        rw [h_add]
        exact ih (acc) hxs
  exact h_aux xs 0 h
open _root_.P2MLLL.t00ef6f00 renaming h96 → Hex.GramSchmidt.Int.foldl_add_zero
open _root_.P2MLLL.t00ef6f00 renaming h96 → _p2mH96


set_option maxRecDepth 8192
/-- Gram zero-pivot column suffix: if the no-pivot Bareiss pass over the Gram
matrix runs `s` steps without recording a singular step but the pivot entry
`matrix[s][s]` is zero, then every later row's entry in column `s` is zero
too. This is the `h_column_zero` premise consumed by
`noPivotLoop_initial_gram_findPivot?_eq_none_of_column_zero` to discharge the
executable `findPivot? = none` form needed by the row-pivoted Bareiss loop on
the Gram trajectory.

The argument: by the closed row-vector consumer, the represented pivot row has
integer support on indices `≤ s` and inner product zero against `b.row k` for
every `k.val ≤ s` (those matrix entries are either the zero pivot itself or
zeros left by earlier regular elimination steps). Linearity of dot against
`vecMul` over the supported indices then gives `v.dotProduct v = 0`,
and integer positive definiteness forces every dot against `v` to be zero.
Trailing-block symmetry transports
`state.matrix[sFin][i] = v.dotProduct (b.row i) = 0` across the diagonal to
`state.matrix[i][sFin] = 0`. -/
 theorem _root_.P2MLLL.t00ef6f00.h114
    {n m : Nat} (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (hquot : StepWitness b)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (h_zero :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0) :
    ∀ i : Fin n, s + 1 ≤ i.val →
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0 := by
  intro i hi
  let sFin : Fin n := ⟨s, Nat.lt_of_succ_lt hs⟩
  -- Final state of the loop and its `step = s` alignment.
  have h_step :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step = s :=
    _root_.P2MLLL.t00ef6f00.h12 b s hs h_prefix_none
  have h_state_step_le_sFin :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ sFin.val := by
    rw [h_step]; show s ≤ s; exact Nat.le_refl _
  -- The row-vector consumer aligns `matrix[sFin][j]` with
  -- `v.dotProduct (b.row j)` for all columns `j`.
  obtain ⟨v, ⟨c, h_coeff_supp_above, hv_def⟩, h_dot_eq_matrix⟩ :=
    _root_.P2MLLL.t00ef6f00.h112 b s hquot sFin h_state_step_le_sFin
  -- The represented row is orthogonal to `b.row k` for every `k.val ≤ s`:
  -- on `k.val = s`, the hypothesis `h_zero` gives a zero pivot dot, and on
  -- `k.val < s` the column was cleared by an earlier regular Bareiss step.
  have h_dot_zero_le : ∀ k : Fin n, k.val ≤ s →
      v.dotProduct (b.row k) = 0 := by
    intro k hks
    rw [← h_dot_eq_matrix k]
    by_cases hk_eq : k.val = s
    · have h_k_eq_sFin : k = sFin := Fin.ext hk_eq
      rw [h_k_eq_sFin]
      exact h_zero
    · -- k.val < s, use column-zero helper at fuel = s, k as kFin, sFin as i.
      have hk_lt : k.val < s := Nat.lt_of_le_of_ne hks hk_eq
      have h_init_step_le :
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ k.val := by
        show 0 ≤ k.val
        exact Nat.zero_le _
      have h_k_lt_result :
          k.val < (Matrix.noPivotLoop s
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step := by
        rw [h_step]
        exact hk_lt
      have h_k_lt_sFin : k.val < sFin.val := hk_lt
      exact _root_.Hex.GramSchmidt.Int.noPivotLoop_matrix_processed_col_eq_zero s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_prefix_none
        k.val h_init_step_le h_k_lt_result k rfl sFin h_k_lt_sFin
  -- `v.dotProduct v = 0`: every term in the vecMul is expansion zero.
  have h_dot_self_zero : v.dotProduct v = 0 := by
    have h_expand_aux :
        v.dotProduct (Matrix.vecMul c b) =
          (List.finRange n).foldl
            (fun acc k => acc + c[k] * v.dotProduct (b.row k))
            0 := by
      have h := _root_.P2MLLL.t00ef6f00.h94 b v c
      rwa [Fin.foldl_eq_finRange_foldl] at h
    rw [← hv_def] at h_expand_aux
    rw [h_expand_aux]
    apply _root_.P2MLLL.t00ef6f00.h96
    intro k _hk
    by_cases hks : k.val ≤ s
    · -- second factor is zero
      rw [h_dot_zero_le k hks]
      grind
    · -- first factor is zero
      have hk_gt : sFin.val < k.val := by show s < k.val; omega
      rw [h_coeff_supp_above k hk_gt]
      grind
  -- Transport across symmetry: `matrix[i][sFin] = matrix[sFin][i]`.
  have h_init_sym :
      ∀ a c : Fin n,
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ a.val →
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ c.val →
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[a][c] =
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[c][a] := by
    intros a c _ha _hc
    show (Matrix.gramMatrix b)[a][c] = (Matrix.gramMatrix b)[c][a]
    rw [Matrix.getElem_gramMatrix, Matrix.getElem_gramMatrix]
    exact _root_.P2MLLL.t00ef6f00.h104 (Matrix.row b a) (Matrix.row b c)
  have h_symm :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][sFin] =
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[sFin][i] := by
    apply _root_.P2MLLL.t00ef6f00.h123 s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_init_sym i sFin
    · rw [h_step]; omega
    · rw [h_step]; show s ≤ s; exact Nat.le_refl _
  -- Now matrix[sFin][i] = dot v (b.row i) = 0 via integer positive definiteness.
  rw [h_symm, h_dot_eq_matrix i]
  exact _root_.P2MLLL.t00ef6f00.h105 (b.row i) v h_dot_self_zero
open _root_.P2MLLL.t00ef6f00 renaming h114 → Hex.GramSchmidt.Int.principalSubmatrix_gram_zero_pivot_column_zero
open _root_.P2MLLL.t00ef6f00 renaming h114 → _p2mH114


set_option maxRecDepth 8192
/-- Substitution helper for the diagonal `(i, i)` matrix entry under a Fin
equality. -/
 theorem _root_.P2MLLL.t00ef6f00.h109 {n : Nat} (M : Matrix Int n n)
    {i j : Fin n} (h : i = j) :
    M[i][i] = M[j][j] := by
  subst h; rfl
open _root_.P2MLLL.t00ef6f00 renaming h109 → Hex.GramSchmidt.Int.matrix_diag_at_fin_eq
open _root_.P2MLLL.t00ef6f00 renaming h109 → _p2mH109


set_option maxRecDepth 8192
/-- If the `a`-fueled no-pivot Bareiss prefix already recorded a singular step,
that step persists into any longer pass. -/
 theorem _root_.P2MLLL.t00ef6f00.h110
    {n : Nat} (state : Matrix.BareissState Int n) (a b : Nat) (k : Fin n)
    (h_sing_a : (Matrix.noPivotLoop a state).singularStep = some k.val)
    (h_step_a : (Matrix.noPivotLoop a state).step = k.val)
    (h_zero_a : (Matrix.noPivotLoop a state).matrix[k][k] = 0)
    (hk : k.val + 1 < n) :
    Matrix.noPivotLoop (a + b) state = Matrix.noPivotLoop a state := by
  rw [Matrix.noPivotLoop_add a b state]
  have hDone : (Matrix.noPivotLoop a state).step + 1 < n := by
    rw [h_step_a]; exact hk
  have hp_zero :
      (Matrix.noPivotLoop a state).matrix[
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
    have h_fin :
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step_a
    exact (_root_.P2MLLL.t00ef6f00.h109 (Matrix.noPivotLoop a state).matrix h_fin).trans h_zero_a
  have h_sing_step : (Matrix.noPivotLoop a state).singularStep =
      some (Matrix.noPivotLoop a state).step := by
    rw [h_sing_a, h_step_a]
  exact Matrix.noPivotLoop_id_at_singular_fixedpoint (n := n) b
    (Matrix.noPivotLoop a state) hDone hp_zero h_sing_step
open _root_.P2MLLL.t00ef6f00 renaming h110 → Hex.GramSchmidt.Int.noPivotLoop_extends_singularStep
open _root_.P2MLLL.t00ef6f00 renaming h110 → _p2mH110


set_option maxRecDepth 8192
/-- From a partial no-pivot Bareiss pass on `M` recording a singular step at
index `s`, derive that the `s`-fueled prefix is non-singular, has reached
`step = s`, and has zero diagonal at `(s, s)`. -/
 theorem _root_.P2MLLL.t00ef6f00.h113
    {n : Nat} (M : Matrix Int n n) (fuel s : Nat) (hs : s + 1 ≤ n)
    (h_sing : (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState M)).singularStep = some s) :
    (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).singularStep = none ∧
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s ∧
      (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState M)).matrix[
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)][
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)] = 0 := by
  have h_init_sing : (Matrix.noPivotInitialState M).singularStep = none := rfl
  have h_init_step : (Matrix.noPivotInitialState M).step = 0 := rfl
  have hsfuel : s < fuel := by
    have := _root_.P2MLLL.t00ef6f00.h2 (n := n) fuel
      (Matrix.noPivotInitialState M) h_init_sing s h_sing
    rw [h_init_step] at this
    omega
  rcases noPivotLoop_singular_inv (n := n) s
      (Matrix.noPivotInitialState M) h_init_sing
    with h_none | ⟨k', h_sing_s, h_step_s, h_zero_s, h_klt⟩
  · have hS_step : (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s := by
      have h_room :
          (Matrix.noPivotInitialState M).step + s + 1 ≤ n := by
        rw [h_init_step]; omega
      have h_step := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        (n := n) s (Matrix.noPivotInitialState M) h_init_sing h_room h_none
      rw [h_step, h_init_step]; omega
    refine ⟨h_none, hS_step, ?_⟩
    rcases noPivotLoop_singular_inv (n := n) fuel
        (Matrix.noPivotInitialState M) h_init_sing
      with h_full_none | ⟨k, h_sing_full, h_step_full, h_zero_full, h_klt_full⟩
    · rw [h_full_none] at h_sing; nomatch h_sing
    · have hk_eq : k.val = s := by
        rw [h_sing_full] at h_sing
        exact Option.some.inj h_sing
      have hsn : s < n := Nat.lt_of_succ_le hs
      have h_full_eq :
          Matrix.noPivotLoop (s + (fuel - s)) (Matrix.noPivotInitialState M) =
            Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) := by
        congr 1; omega
      have h_split :
          Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) =
            Matrix.noPivotLoop (fuel - s)
              (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)) := by
        rw [← h_full_eq,
          Matrix.noPivotLoop_add s (fuel - s) (Matrix.noPivotInitialState M)]
      have h_diag_preserved :
          (Matrix.noPivotLoop (fuel - s)
              (Matrix.noPivotLoop s (Matrix.noPivotInitialState M))).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
        _root_.P2MLLL.t00ef6f00.h5 (fuel - s)
          (Matrix.noPivotLoop s (Matrix.noPivotInitialState M))
          (⟨s, hsn⟩ : Fin n)
          (by rw [hS_step]; exact Nat.le_refl _)
      have h_full_diag_eq :
          (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] := by
        rw [h_split]; exact h_diag_preserved
      have h_fin : k = (⟨s, hsn⟩ : Fin n) := Fin.ext hk_eq
      have h_full_zero :
          (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix[
            (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] = 0 :=
        (_root_.P2MLLL.t00ef6f00.h109
            (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix h_fin).symm.trans
          h_zero_full
      exact h_full_diag_eq.symm.trans h_full_zero
  · have h_klt' : k'.val < s := by
      have := _root_.P2MLLL.t00ef6f00.h2 (n := n) s
        (Matrix.noPivotInitialState M) h_init_sing k'.val h_sing_s
      rw [h_init_step] at this
      omega
    have h_persist :
        Matrix.noPivotLoop (s + (fuel - s)) (Matrix.noPivotInitialState M) =
          Matrix.noPivotLoop s (Matrix.noPivotInitialState M) :=
      _root_.P2MLLL.t00ef6f00.h110 (Matrix.noPivotInitialState M) s (fuel - s) k'
        h_sing_s h_step_s h_zero_s h_klt
    have h_fuel_eq : s + (fuel - s) = fuel := by omega
    rw [h_fuel_eq] at h_persist
    rw [h_persist] at h_sing
    rw [h_sing_s] at h_sing
    have hk'_eq : k'.val = s := Option.some.inj h_sing
    omega
open _root_.P2MLLL.t00ef6f00 renaming h113 → Hex.GramSchmidt.Int.noPivotLoop_prefix_state_at_singular
open _root_.P2MLLL.t00ef6f00 renaming h113 → _p2mH113






set_option maxRecDepth 8192
/-- If the array loop's `state.step` is past the matrix extent, one outer
iteration returns the input state unchanged. -/
 theorem _root_.P2MLLL.t00ef6f00.h116 (fuel : Nat)
    (state : ScaledCoeffArrayState) (hDone : ¬ state.step < n) :
    scaledCoeffArrayLoop n (fuel + 1) state = state := by
  simp [scaledCoeffArrayLoop, hDone]
open _root_.P2MLLL.t00ef6f00 renaming h116 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_done
open _root_.P2MLLL.t00ef6f00 renaming h116 → _p2mH116


set_option maxRecDepth 8192
/-- The array loop is idempotent once `state.step ≥ n`. -/
 theorem _root_.P2MLLL.t00ef6f00.h117 (fuel : Nat)
    (state : ScaledCoeffArrayState) (hDone : ¬ state.step < n) :
    scaledCoeffArrayLoop n fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ f => exact _root_.P2MLLL.t00ef6f00.h116 f state hDone
open _root_.P2MLLL.t00ef6f00 renaming h117 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_id_at_done
open _root_.P2MLLL.t00ef6f00 renaming h117 → _p2mH117


set_option maxRecDepth 8192
/-- Singular branch of one array-loop iteration: a zero pivot strictly before
the last column halts the loop, writing the scaled column at the current step
but leaving the matrix and step untouched. -/
 theorem _root_.P2MLLL.t00ef6f00.h120 (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step = 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      { state with coeffs := writeScaledColumn state.coeffs state.matrix n state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]
open _root_.P2MLLL.t00ef6f00 renaming h120 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_of_singular
open _root_.P2MLLL.t00ef6f00 renaming h120 → _p2mH120


set_option maxRecDepth 8192
/-- Last-column branch of one array-loop iteration: when `state.step = n - 1`,
the loop writes the final scaled column and advances `step` to `n` without
applying a Bareiss step. -/
 theorem _root_.P2MLLL.t00ef6f00.h118 (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : ¬ state.step + 1 < n) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      { state with
        step := state.step + 1
        coeffs := writeScaledColumn state.coeffs state.matrix n state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext]
open _root_.P2MLLL.t00ef6f00 renaming h118 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_last_step
open _root_.P2MLLL.t00ef6f00 renaming h118 → _p2mH118


set_option maxRecDepth 8192
/-- Regular branch of one array-loop iteration: a nonzero pivot strictly before
the last column applies one row-mutating Bareiss update, advances
`step`, records the new `prevPivot`, and recurses on the remaining fuel. -/
 theorem _root_.P2MLLL.t00ef6f00.h119 (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step ≠ 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      scaledCoeffArrayLoop n fuel
        { step := state.step + 1
          matrix := stepScaledRows state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]
open _root_.P2MLLL.t00ef6f00 renaming h119 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_of_regular
open _root_.P2MLLL.t00ef6f00 renaming h119 → _p2mH119


set_option maxRecDepth 8192
/-- The matrix-side view of a row-storage entry: `getArrayEntry` on the array
matches the matrix-level `[i][j]` lookup under `rowsToMatrix`. -/
 theorem _root_.P2MLLL.t00ef6f00.h101
    (rows : Array (Array Int)) (i j : Fin n) :
    getArrayEntry rows i.val j.val = (rowsToMatrix rows n)[i][j] := by
  rw [rowsToMatrix, Matrix.getElem_ofFn]
open _root_.P2MLLL.t00ef6f00 renaming h101 → Hex.GramSchmidt.Int.getArrayEntry_eq_rowsToMatrix
open _root_.P2MLLL.t00ef6f00 renaming h101 → _p2mH101


set_option maxRecDepth 8192
/-- If the array loop is currently at column `j`, the coefficient entry below
the diagonal in that column records the pre-elimination matrix entry for that
same step. In the regular branch, later recursive iterations preserve column
`j` because the next state has advanced past it. -/
 theorem _root_.P2MLLL.t00ef6f00.h102
    (n fuel : Nat) (state : ScaledCoeffArrayState) (i j : Nat)
    (hstep : state.step = j) (hji : j < i) (hin : i < n)
    (h_coeffs_size : state.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state.coeffs[r]!.size = n) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state).coeffs i j =
      getArrayEntry state.matrix i j := by
  have hArrayStep : state.step < n := by omega
  have hrow : i < state.coeffs.size := by
    rw [h_coeffs_size]
    exact hin
  have hcol : j < state.coeffs[i]!.size := by
    rw [h_coeffs_rows_size i hin]
    exact Nat.lt_trans hji hin
  by_cases hNext : state.step + 1 < n
  · by_cases hp : getArrayEntry state.matrix state.step state.step = 0
    · rw [_root_.P2MLLL.t00ef6f00.h120 fuel state hArrayStep hNext hp]
      rw [hstep]
      exact _root_.P2MLLL.t00ef6f00.h56 state.coeffs state.matrix n j i
        hji hin hrow hcol
    · rw [_root_.P2MLLL.t00ef6f00.h119 fuel state hArrayStep hNext hp]
      let next : ScaledCoeffArrayState :=
        { step := state.step + 1
          matrix := stepScaledRows state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step }
      change getArrayEntry (scaledCoeffArrayLoop n fuel next).coeffs i j =
        getArrayEntry state.matrix i j
      rw [_root_.P2MLLL.t00ef6f00.h36]
      · show getArrayEntry (writeScaledColumn state.coeffs state.matrix n state.step) i j =
          getArrayEntry state.matrix i j
        rw [hstep]
        exact _root_.P2MLLL.t00ef6f00.h56 state.coeffs state.matrix n j i
          hji hin hrow hcol
      · show j < next.step
        simp [next, hstep]
  · rw [_root_.P2MLLL.t00ef6f00.h118 fuel state hArrayStep hNext]
    rw [hstep]
    exact _root_.P2MLLL.t00ef6f00.h56 state.coeffs state.matrix n j i
      hji hin hrow hcol
open _root_.P2MLLL.t00ef6f00 renaming h102 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffArrayLoop_current_col_written
open _root_.P2MLLL.t00ef6f00 renaming h102 → _p2mH102


set_option maxRecDepth 8192
/-- Size preservation: the inner `coeffs` array of the scaled-coefficient
array loop keeps its outer-array length. -/
 theorem _root_.P2MLLL.t00ef6f00.h115
    (fuel : Nat) (state : ScaledCoeffArrayState) :
    (scaledCoeffArrayLoop n fuel state).coeffs.size = state.coeffs.size := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      unfold scaledCoeffArrayLoop
      by_cases h_step : state.step < n
      · simp only [h_step, ↓reduceIte]
        by_cases h_next : state.step + 1 < n
        · simp only [h_next, ↓reduceIte]
          by_cases h_pivot : getArrayEntry state.matrix state.step state.step = 0
          · simp only [h_pivot, ↓reduceIte]
            exact _root_.P2MLLL.t00ef6f00.h84 _ _ _ _
          · simp only [h_pivot, ↓reduceIte]
            rw [ih]
            exact _root_.P2MLLL.t00ef6f00.h84 _ _ _ _
        · simp only [h_next, ↓reduceIte]
          exact _root_.P2MLLL.t00ef6f00.h84 _ _ _ _
      · simp only [h_step, ↓reduceIte]
open _root_.P2MLLL.t00ef6f00 renaming h115 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_coeffs_size
open _root_.P2MLLL.t00ef6f00 renaming h115 → _p2mH115


end GramSchmidt.Int
open _root_.P2MLLL.t00ef6f00 renaming h93 → Hex.GramSchmidt.Int.bareissGramRowInvariant_noPivotLoop_initial_canonical
open _root_.P2MLLL.t00ef6f00 renaming h93 → _p2mH93
open _root_.P2MLLL.t00ef6f00 renaming h94 → Hex.GramSchmidt.Int.dot_vecMul_right_eq
open _root_.P2MLLL.t00ef6f00 renaming h94 → _p2mH94
open _root_.P2MLLL.t00ef6f00 renaming h95 → Hex.GramSchmidt.Int.foldl_add_pointwise_eq_int
open _root_.P2MLLL.t00ef6f00 renaming h95 → _p2mH95
open _root_.P2MLLL.t00ef6f00 renaming h96 → Hex.GramSchmidt.Int.foldl_add_zero
open _root_.P2MLLL.t00ef6f00 renaming h96 → _p2mH96
open _root_.P2MLLL.t00ef6f00 renaming h97 → Hex.GramSchmidt.Int.foldl_dot_comm_int_local
open _root_.P2MLLL.t00ef6f00 renaming h97 → _p2mH97
open _root_.P2MLLL.t00ef6f00 renaming h98 → Hex.GramSchmidt.Int.foldl_int_dot_self_eq_zero_of_mem
open _root_.P2MLLL.t00ef6f00 renaming h98 → _p2mH98
open _root_.P2MLLL.t00ef6f00 renaming h99 → Hex.GramSchmidt.Int.foldl_int_dot_self_start_le
open _root_.P2MLLL.t00ef6f00 renaming h99 → _p2mH99
open _root_.P2MLLL.t00ef6f00 renaming h100 → Hex.GramSchmidt.Int.foldl_mul_distrib_int
open _root_.P2MLLL.t00ef6f00 renaming h100 → _p2mH100
open _root_.P2MLLL.t00ef6f00 renaming h101 → Hex.GramSchmidt.Int.getArrayEntry_eq_rowsToMatrix
open _root_.P2MLLL.t00ef6f00 renaming h101 → _p2mH101
open _root_.P2MLLL.t00ef6f00 renaming h102 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffArrayLoop_current_col_written
open _root_.P2MLLL.t00ef6f00 renaming h102 → _p2mH102
open _root_.P2MLLL.t00ef6f00 renaming h103 → Hex.GramSchmidt.Int.getElem_vecMul_int
open _root_.P2MLLL.t00ef6f00 renaming h103 → _p2mH103
open _root_.P2MLLL.t00ef6f00 renaming h104 → Hex.GramSchmidt.Int.int_dot_comm_local
open _root_.P2MLLL.t00ef6f00 renaming h104 → _p2mH104
open _root_.P2MLLL.t00ef6f00 renaming h105 → Hex.GramSchmidt.Int.int_dot_eq_zero_of_dot_self_zero_left
open _root_.P2MLLL.t00ef6f00 renaming h105 → _p2mH105
open _root_.P2MLLL.t00ef6f00 renaming h106 → Hex.GramSchmidt.Int.int_dot_self_eq_zero_get
open _root_.P2MLLL.t00ef6f00 renaming h106 → _p2mH106
open _root_.P2MLLL.t00ef6f00 renaming h107 → Hex.GramSchmidt.Int.int_mul_self_eq_zero_of_nonpos
open _root_.P2MLLL.t00ef6f00 renaming h107 → _p2mH107
open _root_.P2MLLL.t00ef6f00 renaming h108 → Hex.GramSchmidt.Int.int_mul_self_nonneg
open _root_.P2MLLL.t00ef6f00 renaming h108 → _p2mH108
open _root_.P2MLLL.t00ef6f00 renaming h109 → Hex.GramSchmidt.Int.matrix_diag_at_fin_eq
open _root_.P2MLLL.t00ef6f00 renaming h109 → _p2mH109
open _root_.P2MLLL.t00ef6f00 renaming h110 → Hex.GramSchmidt.Int.noPivotLoop_extends_singularStep
open _root_.P2MLLL.t00ef6f00 renaming h110 → _p2mH110
open _root_.P2MLLL.t00ef6f00 renaming h111 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_bareiss_step_dvd
open _root_.P2MLLL.t00ef6f00 renaming h111 → _p2mH111
open _root_.P2MLLL.t00ef6f00 renaming h112 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_exists_rowVec
open _root_.P2MLLL.t00ef6f00 renaming h112 → _p2mH112
open _root_.P2MLLL.t00ef6f00 renaming h113 → Hex.GramSchmidt.Int.noPivotLoop_prefix_state_at_singular
open _root_.P2MLLL.t00ef6f00 renaming h113 → _p2mH113
open _root_.P2MLLL.t00ef6f00 renaming h114 → Hex.GramSchmidt.Int.principalSubmatrix_gram_zero_pivot_column_zero
open _root_.P2MLLL.t00ef6f00 renaming h114 → _p2mH114
open _root_.P2MLLL.t00ef6f00 renaming h115 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_coeffs_size
open _root_.P2MLLL.t00ef6f00 renaming h115 → _p2mH115
open _root_.P2MLLL.t00ef6f00 renaming h116 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_done
open _root_.P2MLLL.t00ef6f00 renaming h116 → _p2mH116
open _root_.P2MLLL.t00ef6f00 renaming h117 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_id_at_done
open _root_.P2MLLL.t00ef6f00 renaming h117 → _p2mH117
open _root_.P2MLLL.t00ef6f00 renaming h118 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_last_step
open _root_.P2MLLL.t00ef6f00 renaming h118 → _p2mH118
open _root_.P2MLLL.t00ef6f00 renaming h119 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_of_regular
open _root_.P2MLLL.t00ef6f00 renaming h119 → _p2mH119
open _root_.P2MLLL.t00ef6f00 renaming h120 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_of_singular
open _root_.P2MLLL.t00ef6f00 renaming h120 → _p2mH120

end Hex
open _root_.P2MLLL.t00ef6f00 renaming h93 → Hex.GramSchmidt.Int.bareissGramRowInvariant_noPivotLoop_initial_canonical
open _root_.P2MLLL.t00ef6f00 renaming h93 → _p2mH93
open _root_.P2MLLL.t00ef6f00 renaming h94 → Hex.GramSchmidt.Int.dot_vecMul_right_eq
open _root_.P2MLLL.t00ef6f00 renaming h94 → _p2mH94
open _root_.P2MLLL.t00ef6f00 renaming h95 → Hex.GramSchmidt.Int.foldl_add_pointwise_eq_int
open _root_.P2MLLL.t00ef6f00 renaming h95 → _p2mH95
open _root_.P2MLLL.t00ef6f00 renaming h96 → Hex.GramSchmidt.Int.foldl_add_zero
open _root_.P2MLLL.t00ef6f00 renaming h96 → _p2mH96
open _root_.P2MLLL.t00ef6f00 renaming h97 → Hex.GramSchmidt.Int.foldl_dot_comm_int_local
open _root_.P2MLLL.t00ef6f00 renaming h97 → _p2mH97
open _root_.P2MLLL.t00ef6f00 renaming h98 → Hex.GramSchmidt.Int.foldl_int_dot_self_eq_zero_of_mem
open _root_.P2MLLL.t00ef6f00 renaming h98 → _p2mH98
open _root_.P2MLLL.t00ef6f00 renaming h99 → Hex.GramSchmidt.Int.foldl_int_dot_self_start_le
open _root_.P2MLLL.t00ef6f00 renaming h99 → _p2mH99
open _root_.P2MLLL.t00ef6f00 renaming h100 → Hex.GramSchmidt.Int.foldl_mul_distrib_int
open _root_.P2MLLL.t00ef6f00 renaming h100 → _p2mH100
open _root_.P2MLLL.t00ef6f00 renaming h101 → Hex.GramSchmidt.Int.getArrayEntry_eq_rowsToMatrix
open _root_.P2MLLL.t00ef6f00 renaming h101 → _p2mH101
open _root_.P2MLLL.t00ef6f00 renaming h102 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffArrayLoop_current_col_written
open _root_.P2MLLL.t00ef6f00 renaming h102 → _p2mH102
open _root_.P2MLLL.t00ef6f00 renaming h103 → Hex.GramSchmidt.Int.getElem_vecMul_int
open _root_.P2MLLL.t00ef6f00 renaming h103 → _p2mH103
open _root_.P2MLLL.t00ef6f00 renaming h104 → Hex.GramSchmidt.Int.int_dot_comm_local
open _root_.P2MLLL.t00ef6f00 renaming h104 → _p2mH104
open _root_.P2MLLL.t00ef6f00 renaming h105 → Hex.GramSchmidt.Int.int_dot_eq_zero_of_dot_self_zero_left
open _root_.P2MLLL.t00ef6f00 renaming h105 → _p2mH105
open _root_.P2MLLL.t00ef6f00 renaming h106 → Hex.GramSchmidt.Int.int_dot_self_eq_zero_get
open _root_.P2MLLL.t00ef6f00 renaming h106 → _p2mH106
open _root_.P2MLLL.t00ef6f00 renaming h107 → Hex.GramSchmidt.Int.int_mul_self_eq_zero_of_nonpos
open _root_.P2MLLL.t00ef6f00 renaming h107 → _p2mH107
open _root_.P2MLLL.t00ef6f00 renaming h108 → Hex.GramSchmidt.Int.int_mul_self_nonneg
open _root_.P2MLLL.t00ef6f00 renaming h108 → _p2mH108
open _root_.P2MLLL.t00ef6f00 renaming h109 → Hex.GramSchmidt.Int.matrix_diag_at_fin_eq
open _root_.P2MLLL.t00ef6f00 renaming h109 → _p2mH109
open _root_.P2MLLL.t00ef6f00 renaming h110 → Hex.GramSchmidt.Int.noPivotLoop_extends_singularStep
open _root_.P2MLLL.t00ef6f00 renaming h110 → _p2mH110
open _root_.P2MLLL.t00ef6f00 renaming h111 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_bareiss_step_dvd
open _root_.P2MLLL.t00ef6f00 renaming h111 → _p2mH111
open _root_.P2MLLL.t00ef6f00 renaming h112 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_exists_rowVec
open _root_.P2MLLL.t00ef6f00 renaming h112 → _p2mH112
open _root_.P2MLLL.t00ef6f00 renaming h113 → Hex.GramSchmidt.Int.noPivotLoop_prefix_state_at_singular
open _root_.P2MLLL.t00ef6f00 renaming h113 → _p2mH113
open _root_.P2MLLL.t00ef6f00 renaming h114 → Hex.GramSchmidt.Int.principalSubmatrix_gram_zero_pivot_column_zero
open _root_.P2MLLL.t00ef6f00 renaming h114 → _p2mH114
open _root_.P2MLLL.t00ef6f00 renaming h115 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_coeffs_size
open _root_.P2MLLL.t00ef6f00 renaming h115 → _p2mH115
open _root_.P2MLLL.t00ef6f00 renaming h116 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_done
open _root_.P2MLLL.t00ef6f00 renaming h116 → _p2mH116
open _root_.P2MLLL.t00ef6f00 renaming h117 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_id_at_done
open _root_.P2MLLL.t00ef6f00 renaming h117 → _p2mH117
open _root_.P2MLLL.t00ef6f00 renaming h118 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_last_step
open _root_.P2MLLL.t00ef6f00 renaming h118 → _p2mH118
open _root_.P2MLLL.t00ef6f00 renaming h119 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_of_regular
open _root_.P2MLLL.t00ef6f00 renaming h119 → _p2mH119
open _root_.P2MLLL.t00ef6f00 renaming h120 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_of_singular
open _root_.P2MLLL.t00ef6f00 renaming h120 → _p2mH120


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
Correspondence between the executable `scaledCoeffRows` pass and the
matrix-level Gram-determinant API for `hex-gram-schmidt`.

This module proves that the array-storage scaled-coefficient loop tracks the
matrix-level no-pivot Bareiss pass entry for entry: the diagonal slots record
the leading Gram determinants (`gramDetVecEntry_eq_gramDet`,
`scaledCoeffRows_diag_toNat_eq_gramDet`) including the zero tail after an early
singular step, and the lower-triangle slots capture the corresponding Bareiss
target-column values. It exposes the determinant base case `gramDet_zero`, the
lower-triangularity of the public matrix (`scaledCoeffs_upper`), and the
lattice-norm helper `vecMul_coeffs_apply_eq_of_zero_above` giving the
top Gram-Schmidt coordinate of a row combination when the later integer
coefficients vanish.
-/
namespace Hex
namespace GramSchmidt.Int
set_option maxRecDepth 8192
/-- Bareiss-side counterpart of the Schur `j = 0` boundary: at column `0`,
the scaled-coefficient array records the gram entry `gram[i][0]` at every
row `i`. The first `writeScaledColumn` call captures the initial gram column;
subsequent loop iterations advance past column `0` and preserve it. -/
 theorem _root_.P2MLLL.t00ef6f00.h88
    (b : Matrix Int n m) (i : Nat) :
    getArrayEntry (scaledCoeffRows b) i 0 =
      getArrayEntry (gramRows b) i 0 := by
  by_cases hin : i < n
  · -- In bounds. n ≥ 1 (since `i < n`), so the array loop unfolds at least
    -- one step. The first iteration writes column 0 from `gramRows b`, and
    -- later iterations have `step ≥ 1` so they preserve column 0.
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hin
    obtain ⟨fuel, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h_coeffs_size : (zeroRows (fuel + 1)).size = fuel + 1 := _root_.P2MLLL.t00ef6f00.h86 _
    have h_coeffs_row_size :
        ∀ r, r < fuel + 1 → (zeroRows (fuel + 1))[r]!.size = fuel + 1 :=
      fun r hr => _root_.P2MLLL.t00ef6f00.h85 _ r hr
    let initState : ScaledCoeffArrayState :=
      { step := 0, matrix := gramRows b, coeffs := zeroRows (fuel + 1),
        prevPivot := 1 }
    by_cases hi : i = 0
    · -- Diagonal case: (0, 0). Unfold one step and use writeScaledColumn_diag.
      subst hi
      have hrow : (0 : Nat) < (zeroRows (fuel + 1)).size := by
        rw [h_coeffs_size]; exact hn
      have hcol : (0 : Nat) < (zeroRows (fuel + 1))[0]!.size := by
        rw [_root_.P2MLLL.t00ef6f00.h85 _ 0 hn]; exact hn
      show getArrayEntry (scaledCoeffArrayLoop (fuel + 1) (fuel + 1) initState).coeffs 0 0
          = getArrayEntry (gramRows b) 0 0
      by_cases hNext : (0 : Nat) + 1 < fuel + 1
      · by_cases hp : getArrayEntry (gramRows b) 0 0 = 0
        · rw [_root_.P2MLLL.t00ef6f00.h120 (n := fuel + 1) fuel initState hn hNext hp]
          exact _root_.P2MLLL.t00ef6f00.h57 _ _ _ _ hrow hcol
        · rw [_root_.P2MLLL.t00ef6f00.h119 (n := fuel + 1) fuel initState hn hNext hp]
          rw [_root_.P2MLLL.t00ef6f00.h36
                (n := fuel + 1) fuel _ 0 0 (show (0 : Nat) < 0 + 1 by omega)]
          exact _root_.P2MLLL.t00ef6f00.h57 _ _ _ _ hrow hcol
      · rw [_root_.P2MLLL.t00ef6f00.h118 (n := fuel + 1) fuel initState hn hNext]
        exact _root_.P2MLLL.t00ef6f00.h57 _ _ _ _ hrow hcol
    · -- Strict lower (0 < i < n). Reuse the existing current-col capture lemma.
      have hji : 0 < i := Nat.pos_of_ne_zero hi
      show getArrayEntry (scaledCoeffArrayLoop (fuel + 1) (fuel + 1) initState).coeffs i 0
          = getArrayEntry (gramRows b) i 0
      exact _root_.P2MLLL.t00ef6f00.h102
        (n := fuel + 1) fuel initState i 0 (by rfl) hji hin h_coeffs_size h_coeffs_row_size
  · -- Out of bounds. The array loop never grows `coeffs.size`, so `(i, 0)`
    -- stays at the initial zero (and so does `(gramRows b)[i][0]`).
    have hin' : n ≤ i := Nat.le_of_not_lt hin
    have h_final_size : (scaledCoeffRows b).size = n := by
      unfold scaledCoeffRows
      rw [_root_.P2MLLL.t00ef6f00.h115]
      exact _root_.P2MLLL.t00ef6f00.h86 n
    have h_gram_size : (gramRows b).size = n := _root_.P2MLLL.t00ef6f00.h66 b
    have h_lhs : getArrayEntry (scaledCoeffRows b) i 0 = 0 := by
      have h_size_le : (scaledCoeffRows b).size ≤ i := h_final_size.symm ▸ hin'
      have h_entry_default : (scaledCoeffRows b)[i]! = (default : Array Int) := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none h_size_le, Option.getD_none]
      unfold getArrayEntry
      rw [h_entry_default]
      exact _root_.P2MLLL.t00ef6f00.h28 0
    have h_rhs : getArrayEntry (gramRows b) i 0 = 0 := by
      have h_size_le : (gramRows b).size ≤ i := h_gram_size.symm ▸ hin'
      have h_entry_default : (gramRows b)[i]! = (default : Array Int) := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none h_size_le, Option.getD_none]
      unfold getArrayEntry
      rw [h_entry_default]
      exact _root_.P2MLLL.t00ef6f00.h28 0
    rw [h_lhs, h_rhs]
open _root_.P2MLLL.t00ef6f00 renaming h88 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRows_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h88 → _p2mH88


set_option maxRecDepth 8192
/-- Non-singular target-column lower-triangle capture. If the matrix-side
`noPivotLoop` reaches the target column `j` without recording a singular step,
then the scaled-coefficient array loop records at `(i,j)` the matrix entry from
the pre-elimination state at that target column. -/
 theorem _root_.P2MLLL.t00ef6f00.h90
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState Int n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (h_array_size : state_array.matrix.size = n)
    (h_array_rows_size : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (fuel : Nat) (i j : Fin n)
    (h_step_le_j : state_matrix.step ≤ j.val)
    (hji : j.val < i.val)
    (h_fuel : j.val < state_matrix.step + fuel)
    (h_target_nonsing :
      (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).singularStep = none) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val j.val =
      (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).matrix[i][j] := by
  induction fuel generalizing state_array state_matrix with
  | zero =>
      omega
  | succ fuel' ih =>
      by_cases h_at_target : state_matrix.step = j.val
      · have h_array_step : state_array.step = j.val := by
          rw [h_step_eq, h_at_target]
        rw [_root_.P2MLLL.t00ef6f00.h102 n fuel' state_array
          i.val j.val h_array_step hji i.isLt h_coeffs_size h_coeffs_rows_size]
        have hdist : j.val - state_matrix.step = 0 := by omega
        rw [hdist, Matrix.noPivotLoop_zero_fuel,
          _root_.P2MLLL.t00ef6f00.h101 state_array.matrix i j, h_matrix_eq]
      · have h_step_lt_j : state_matrix.step < j.val :=
          Nat.lt_of_le_of_ne h_step_le_j h_at_target
        have hDone : state_matrix.step + 1 < n := by
          omega
        have h_step_lt_n : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hArrayStep : state_array.step < n := h_step_eq ▸ h_step_lt_n
        have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
        let kFin : Fin n := ⟨state_matrix.step, h_step_lt_n⟩
        have h_pivot_array_eq_matrix :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [h_step_eq]
          have := _root_.P2MLLL.t00ef6f00.h101 (n := n) state_array.matrix kFin kFin
          rw [this, h_matrix_eq]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        · have hdist :
              j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
            omega
          rw [hdist, Matrix.noPivotLoop_of_singular _ state_matrix hDone hp] at h_target_nonsing
          simp at h_target_nonsing
        · have hp_array :
              getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [h_pivot_array_eq_matrix]
            exact hp
          rw [_root_.P2MLLL.t00ef6f00.h119 fuel' state_array hArrayStep hArrayNext hp_array]
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState Int n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          change getArrayEntry (scaledCoeffArrayLoop n fuel' new_array).coeffs i.val j.val =
            (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).matrix[i][j]
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [h_step_eq]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _ state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [_root_.P2MLLL.t00ef6f00.h70 _ _ _ _ h_array_size
              h_array_rows_size, h_matrix_eq, h_pivot_array_eq_matrix, h_step_eq, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot := h_pivot_array_eq_matrix
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [_root_.P2MLLL.t00ef6f00.h82, h_array_size]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _ _)[r]!.size = n
            exact _root_.P2MLLL.t00ef6f00.h81 state_array.matrix n state_array.step _ _
              h_array_size h_array_rows_size r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [_root_.P2MLLL.t00ef6f00.h84]
            exact h_coeffs_size
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [_root_.P2MLLL.t00ef6f00.h83]
            exact h_coeffs_rows_size r hr
          have h_step_le_j_new : new_matrix.step ≤ j.val := by
            show state_matrix.step + 1 ≤ j.val
            omega
          have h_fuel_new : j.val < new_matrix.step + fuel' := by
            show j.val < state_matrix.step + 1 + fuel'
            omega
          have h_target_nonsing_new :
              (Matrix.noPivotLoop (j.val - new_matrix.step) new_matrix).singularStep = none := by
            have hdist :
                j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
              omega
            rw [hdist, Matrix.noPivotLoop_of_regular _ state_matrix hDone hp] at h_target_nonsing
            simpa [new_matrix] using h_target_nonsing
          have h_capture := ih h_step_new h_matrix_new h_prev_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_step_le_j_new h_fuel_new h_target_nonsing_new
          have hdist :
              j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
            omega
          rw [h_capture, hdist, Matrix.noPivotLoop_of_regular _ state_matrix hDone hp]
          rfl
open _root_.P2MLLL.t00ef6f00 renaming h90 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_lower_matches_target_column
open _root_.P2MLLL.t00ef6f00 renaming h90 → _p2mH90


set_option maxRecDepth 8192
/-- Early-singular zero tail after the singular column: if the lower entries
in columns strictly after the current step are still unwritten before the
singular branch, writing the current column preserves that zero tail. -/
 theorem _root_.P2MLLL.t00ef6f00.h91
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState Int n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_coeffs_unwritten : ∀ r c : Fin n,
      state_matrix.step < c.val → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = 0)
    (fuel : Nat) (i j : Fin n)
    (hsj : state_matrix.step < j.val) (hji : j.val < i.val)
    (hDone : state_matrix.step + 1 < n)
    (hp : state_matrix.matrix[
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs i.val j.val = 0 := by
  have hArrayStep : state_array.step < n := h_step_eq ▸ Nat.lt_of_succ_lt hDone
  have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
  let kFin : Fin n := ⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩
  have hp_array :
      getArrayEntry state_array.matrix state_array.step state_array.step = 0 := by
    rw [h_step_eq]
    have := _root_.P2MLLL.t00ef6f00.h101 (n := n) state_array.matrix kFin kFin
    rw [this, h_matrix_eq]
    exact hp
  rw [_root_.P2MLLL.t00ef6f00.h120 fuel state_array hArrayStep hArrayNext hp_array,
    _root_.P2MLLL.t00ef6f00.h54]
  · exact h_coeffs_unwritten i j hsj hji
  · rw [h_step_eq]
    omega
open _root_.P2MLLL.t00ef6f00 renaming h91 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_lower_singular_after_step
open _root_.P2MLLL.t00ef6f00 renaming h91 → _p2mH91


set_option maxRecDepth 8192
/-- Singular dual of `scaledCoeffArrayLoop_lower_matches_target_column`.
When the matrix-side `noPivotLoop` records a singular step strictly before
reaching column `j`, the array loop halts at the singular column and the
target column is left at its initial (unwritten) zero value. -/
 theorem _root_.P2MLLL.t00ef6f00.h92
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState Int n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (h_array_size : state_array.matrix.size = n)
    (h_array_rows_size : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (h_coeffs_unwritten : ∀ r c : Fin n,
      state_matrix.step < c.val → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = 0)
    (h_no_sing : state_matrix.singularStep = none)
    (fuel : Nat) (i j : Fin n)
    (h_step_le_j : state_matrix.step ≤ j.val)
    (hji : j.val < i.val)
    (h_fuel : j.val < state_matrix.step + fuel)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).singularStep
        = some s) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val j.val = 0 := by
  induction fuel generalizing state_array state_matrix with
  | zero => omega
  | succ fuel' ih =>
      by_cases h_at_target : state_matrix.step = j.val
      · have hdist : j.val - state_matrix.step = 0 := by omega
        rw [hdist, Matrix.noPivotLoop_zero_fuel] at h_sing
        rw [h_no_sing] at h_sing
        nomatch h_sing
      · have h_step_lt_j : state_matrix.step < j.val :=
          Nat.lt_of_le_of_ne h_step_le_j h_at_target
        have hDone : state_matrix.step + 1 < n := by
          have := i.isLt
          omega
        have h_step_lt_n : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hArrayStep : state_array.step < n := h_step_eq ▸ h_step_lt_n
        have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
        let kFin : Fin n := ⟨state_matrix.step, h_step_lt_n⟩
        have h_pivot_array_eq_matrix :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [h_step_eq]
          have := _root_.P2MLLL.t00ef6f00.h101 (n := n) state_array.matrix kFin kFin
          rw [this, h_matrix_eq]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        · exact _root_.P2MLLL.t00ef6f00.h91
            (n := n) (state_array := state_array) (state_matrix := state_matrix)
            h_step_eq h_matrix_eq h_coeffs_unwritten fuel' i j h_step_lt_j hji hDone hp
        · have hp_array :
              getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [h_pivot_array_eq_matrix]
            exact hp
          rw [_root_.P2MLLL.t00ef6f00.h119 fuel' state_array hArrayStep
            hArrayNext hp_array]
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n
                state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState Int n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          change getArrayEntry (scaledCoeffArrayLoop n fuel' new_array).coeffs i.val j.val = 0
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [h_step_eq]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _
                  state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [_root_.P2MLLL.t00ef6f00.h70 _ _ _ _ h_array_size
              h_array_rows_size, h_matrix_eq, h_pivot_array_eq_matrix, h_step_eq, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot :=
            h_pivot_array_eq_matrix
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [_root_.P2MLLL.t00ef6f00.h82, h_array_size]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _
              state_array.prevPivot)[r]!.size = n
            exact _root_.P2MLLL.t00ef6f00.h81 state_array.matrix n state_array.step _ _
              h_array_size h_array_rows_size r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [_root_.P2MLLL.t00ef6f00.h84]
            exact h_coeffs_size
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [_root_.P2MLLL.t00ef6f00.h83]
            exact h_coeffs_rows_size r hr
          have h_coeffs_unwritten_new : ∀ r c : Fin n,
              new_matrix.step < c.val → c.val < r.val →
                getArrayEntry new_array.coeffs r.val c.val = 0 := by
            intro r c hsc hcr
            show getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n
                  state_array.step) r.val c.val = 0
            have hsc' : state_matrix.step + 1 < c.val := hsc
            have hc_ne_step : c.val ≠ state_array.step := by
              rw [h_step_eq]; omega
            rw [_root_.P2MLLL.t00ef6f00.h54 _ _ _ _ _ _ hc_ne_step]
            exact h_coeffs_unwritten r c (by omega) hcr
          have h_no_sing_new : new_matrix.singularStep = none := rfl
          have h_step_le_j_new : new_matrix.step ≤ j.val := by
            show state_matrix.step + 1 ≤ j.val
            omega
          have h_fuel_new : j.val < new_matrix.step + fuel' := by
            show j.val < state_matrix.step + 1 + fuel'
            omega
          have h_sing_new :
              (Matrix.noPivotLoop (j.val - new_matrix.step) new_matrix).singularStep
                = some s := by
            have hdist :
                j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
              omega
            rw [hdist, Matrix.noPivotLoop_of_regular _ state_matrix hDone hp] at h_sing
            simpa [new_matrix] using h_sing
          exact ih h_step_new h_matrix_new h_prev_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_coeffs_unwritten_new h_no_sing_new h_step_le_j_new h_fuel_new
            h_sing_new
open _root_.P2MLLL.t00ef6f00 renaming h92 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_lower_zero
open _root_.P2MLLL.t00ef6f00 renaming h92 → _p2mH92


set_option maxRecDepth 8192
/-- State-level diagonal correspondence between the scaled-coefficient array
loop and the matrix-level `Matrix.noPivotLoop` on the same Gram-like data.

After running both loops for `fuel` iterations from compatible starting states
(matching steps, matrices, and `prevPivot`, with no recorded singular step
upstream and the coeffs invariant for already-processed columns), the
diagonal coefficient at every position `i` either matches the matrix-level
diagonal of `noPivotLoop` (when no singular step has been hit at or before
`i`) or is recorded as zero (when singular at some `s ≤ i`). This captures
the loop-level interpretation of `gramDetVecEntry` against the executable
array trajectory. -/
 theorem _root_.P2MLLL.t00ef6f00.h89
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState Int n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (h_no_sing : state_matrix.singularStep = none)
    (h_array_size : state_array.matrix.size = n)
    (h_array_rows_size : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (h_coeffs_processed : ∀ j (_hjs : j < state_matrix.step) (hjn : j < n),
      getArrayEntry state_array.coeffs j j =
        state_matrix.matrix[(⟨j, hjn⟩ : Fin n)][(⟨j, hjn⟩ : Fin n)])
    (h_coeffs_unwritten : ∀ j (_hjs : state_matrix.step ≤ j) (_hjn : j < n),
      getArrayEntry state_array.coeffs j j = 0)
    (fuel : Nat) (i : Fin n)
    (h_fuel : i.val < state_matrix.step + fuel ∨ i.val < state_matrix.step) :
    ((Matrix.noPivotLoop fuel state_matrix).singularStep = none ∧
      getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val =
        (Matrix.noPivotLoop fuel state_matrix).matrix[i][i]) ∨
    (∃ s : Nat,
      (Matrix.noPivotLoop fuel state_matrix).singularStep = some s ∧
      ((s ≤ i.val ∧
        getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val = 0) ∨
       (i.val < s ∧
        getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val =
          (Matrix.noPivotLoop fuel state_matrix).matrix[i][i]))) := by
  induction fuel generalizing state_array state_matrix with
  | zero =>
      left
      refine ⟨h_no_sing, ?_⟩
      have h_ilt : i.val < state_matrix.step := by
        rcases h_fuel with hor1 | hor2
        · simpa using hor1
        · exact hor2
      exact h_coeffs_processed i.val h_ilt i.isLt
  | succ fuel' ih =>
      by_cases hDone : state_matrix.step + 1 < n
      · -- Subcase A: state_matrix.step + 1 < n. One real iteration.
        have h_step_lt_n : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hArrayStep : state_array.step < n := h_step_eq ▸ h_step_lt_n
        have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
        -- Build the pivot Fin index once.
        let kFin : Fin n := ⟨state_matrix.step, h_step_lt_n⟩
        -- Identify pivot equality between array and matrix views.
        have h_pivot_array_eq_matrix :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [h_step_eq]
          have := _root_.P2MLLL.t00ef6f00.h101 (n := n) state_array.matrix kFin kFin
          rw [this, h_matrix_eq]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        · -- A1: singular branch.
          have hp_array : getArrayEntry state_array.matrix state_array.step state_array.step = 0 := by
            rw [h_pivot_array_eq_matrix]; exact hp
          rw [_root_.P2MLLL.t00ef6f00.h120 fuel' state_array hArrayStep hArrayNext hp_array,
            Matrix.noPivotLoop_of_singular fuel' state_matrix hDone hp]
          right
          refine ⟨state_matrix.step, rfl, ?_⟩
          by_cases h_ilt : i.val < state_matrix.step
          · right
            refine ⟨h_ilt, ?_⟩
            change getArrayEntry
              (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
              state_matrix.matrix[i][i]
            rw [_root_.P2MLLL.t00ef6f00.h54 _ _ _ _ _ _
              (show i.val ≠ state_array.step by rw [h_step_eq]; omega)]
            exact h_coeffs_processed i.val h_ilt i.isLt
          · have h_ilt : state_matrix.step ≤ i.val := Nat.le_of_not_lt h_ilt
            by_cases h_ieq : i.val = state_matrix.step
            · left
              refine ⟨Nat.le_of_eq h_ieq.symm, ?_⟩
              change getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                0
              have h_array_step_eq_i : state_array.step = i.val := by
                rw [h_step_eq]; exact h_ieq.symm
              rw [h_array_step_eq_i]
              have hrow : i.val < state_array.coeffs.size := by
                rw [h_coeffs_size]; exact i.isLt
              have hcol : i.val < state_array.coeffs[i.val]!.size := by
                rw [h_coeffs_rows_size i.val i.isLt]; exact i.isLt
              rw [_root_.P2MLLL.t00ef6f00.h57 _ _ _ _ hrow hcol]
              -- Goal: getArrayEntry state_array.matrix i.val i.val = 0
              rw [← h_array_step_eq_i]
              exact hp_array
            · have h_igt : state_matrix.step < i.val :=
                Nat.lt_of_le_of_ne h_ilt fun h => h_ieq h.symm
              left
              refine ⟨Nat.le_of_lt h_igt, ?_⟩
              change getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                0
              rw [_root_.P2MLLL.t00ef6f00.h54 _ _ _ _ _ _
                (show i.val ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_unwritten i.val (Nat.le_of_lt h_igt) i.isLt
        · -- A2: regular branch.
          have hp_array : getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [h_pivot_array_eq_matrix]; exact hp
          rw [_root_.P2MLLL.t00ef6f00.h119 fuel' state_array hArrayStep hArrayNext hp_array,
            Matrix.noPivotLoop_of_regular fuel' state_matrix hDone hp]
          -- Build new compatible states.
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState Int n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [h_step_eq]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _ state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [_root_.P2MLLL.t00ef6f00.h70 _ _ _ _ h_array_size
              h_array_rows_size, h_matrix_eq, h_pivot_array_eq_matrix, h_step_eq, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot := h_pivot_array_eq_matrix
          have h_no_sing_new : new_matrix.singularStep = none := rfl
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [_root_.P2MLLL.t00ef6f00.h82, h_array_size]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _ _)[r]!.size = n
            exact _root_.P2MLLL.t00ef6f00.h81 state_array.matrix n state_array.step _ _
              h_array_size h_array_rows_size r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [_root_.P2MLLL.t00ef6f00.h84]; exact h_coeffs_size
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [_root_.P2MLLL.t00ef6f00.h83]; exact h_coeffs_rows_size r hr
          have h_coeffs_processed_new :
              ∀ j (_hjs : j < new_matrix.step) (hjn : j < n),
                getArrayEntry new_array.coeffs j j =
                  new_matrix.matrix[(⟨j, hjn⟩ : Fin n)][(⟨j, hjn⟩ : Fin n)] := by
            intro j hjs hjn
            let jFin : Fin n := ⟨j, hjn⟩
            change getArrayEntry (writeScaledColumn _ _ _ _) j j =
              (Matrix.stepMatrix state_matrix.matrix _ _ state_matrix.prevPivot)[jFin][jFin]
            have hj_le : jFin.val ≤ state_matrix.step := Nat.le_of_lt_succ hjs
            rw [_root_.P2MLLL.t00ef6f00.h7 _ _ _ _ _ hj_le]
            by_cases hj_eq : j = state_matrix.step
            · -- j = state_matrix.step = state_array.step
              have h_array_step_eq_j : state_array.step = j := h_step_eq.trans hj_eq.symm
              -- Rewrite writeScaledColumn's step argument to use j.
              have h_write_eq :
                  getArrayEntry
                      (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) j j =
                    getArrayEntry
                      (writeScaledColumn state_array.coeffs state_array.matrix n j) j j := by
                rw [h_array_step_eq_j]
              rw [h_write_eq]
              have hrow : j < state_array.coeffs.size := by
                rw [h_coeffs_size]; exact hjn
              have hcol : j < state_array.coeffs[j]!.size := by
                rw [h_coeffs_rows_size j hjn]; exact hjn
              rw [_root_.P2MLLL.t00ef6f00.h57 _ _ _ _ hrow hcol]
              -- Goal: getArrayEntry state_array.matrix j j = state_matrix.matrix[jFin][jFin]
              rw [_root_.P2MLLL.t00ef6f00.h101 state_array.matrix jFin jFin, h_matrix_eq]
            · have hj_lt : j < state_matrix.step := Nat.lt_of_le_of_ne hj_le hj_eq
              rw [_root_.P2MLLL.t00ef6f00.h54 _ _ _ _ _ _
                (show j ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_processed j hj_lt hjn
          have h_coeffs_unwritten_new :
              ∀ j (_hjs : new_matrix.step ≤ j) (_hjn : j < n),
                getArrayEntry new_array.coeffs j j = 0 := by
            intro j hjs hjn
            show getArrayEntry (writeScaledColumn _ _ _ _) j j = 0
            have hj_gt : state_matrix.step < j := hjs
            rw [_root_.P2MLLL.t00ef6f00.h54 _ _ _ _ _ _
              (show j ≠ state_array.step by rw [h_step_eq]; omega)]
            exact h_coeffs_unwritten j (Nat.le_of_lt hj_gt) hjn
          have h_fuel_new : i.val < new_matrix.step + fuel' ∨ i.val < new_matrix.step := by
            show i.val < state_matrix.step + 1 + fuel' ∨ i.val < state_matrix.step + 1
            rcases h_fuel with hor1 | hor2
            · left; omega
            · right; omega
          exact ih h_step_new h_matrix_new h_prev_new h_no_sing_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_coeffs_processed_new h_coeffs_unwritten_new h_fuel_new
      · -- Subcase B: state_matrix.step + 1 ≥ n.
        rw [Matrix.noPivotLoop_done fuel' state_matrix hDone]
        left
        refine ⟨h_no_sing, ?_⟩
        by_cases hArrayStep : state_array.step < n
        · have hArrayNext : ¬ state_array.step + 1 < n := h_step_eq ▸ hDone
          rw [_root_.P2MLLL.t00ef6f00.h118 fuel' state_array hArrayStep hArrayNext]
          by_cases h_ieq : i.val = state_matrix.step
          · have h_array_step_eq_i : state_array.step = i.val := by
              rw [h_step_eq]; exact h_ieq.symm
            change getArrayEntry (writeScaledColumn _ _ _ _) i.val i.val = _
            have h_rewrite_step :
                getArrayEntry
                    (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                  getArrayEntry
                    (writeScaledColumn state_array.coeffs state_array.matrix n i.val) i.val i.val := by
              rw [h_array_step_eq_i]
            rw [h_rewrite_step]
            have hrow : i.val < state_array.coeffs.size := by
              rw [h_coeffs_size]; exact i.isLt
            have hcol : i.val < state_array.coeffs[i.val]!.size := by
              rw [h_coeffs_rows_size i.val i.isLt]; exact i.isLt
            rw [_root_.P2MLLL.t00ef6f00.h57 _ _ _ _ hrow hcol,
              _root_.P2MLLL.t00ef6f00.h101 state_array.matrix i i, h_matrix_eq]
          · by_cases h_ilt : i.val < state_matrix.step
            · change getArrayEntry (writeScaledColumn _ _ _ _) i.val i.val = _
              rw [_root_.P2MLLL.t00ef6f00.h54 _ _ _ _ _ _
                (show i.val ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_processed i.val h_ilt i.isLt
            · have h_ilt : state_matrix.step ≤ i.val := Nat.le_of_not_lt h_ilt
              have h_igt : state_matrix.step < i.val :=
                Nat.lt_of_le_of_ne h_ilt fun h => h_ieq h.symm
              have hDone : ¬ state_matrix.step + 1 < n := hDone
              omega
        · rw [_root_.P2MLLL.t00ef6f00.h117 (fuel' + 1) state_array hArrayStep]
          have hArrayStep' : n ≤ state_array.step := Nat.le_of_not_lt hArrayStep
          have h_ilt : i.val < state_matrix.step := by
            rw [← h_step_eq]; exact Nat.lt_of_lt_of_le i.isLt hArrayStep'
          exact h_coeffs_processed i.val h_ilt i.isLt
open _root_.P2MLLL.t00ef6f00 renaming h89 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_diag_matches
open _root_.P2MLLL.t00ef6f00 renaming h89 → _p2mH89














set_option maxRecDepth 8192
/-- Both `scaledCoeffRows` and `scaledCoeffRowsSchur` start from `zeroRows n`
and only write strict-lower / diagonal entries; the upper-triangle slot at
`(i, j)` with `i < j` therefore retains its initial zero value, regardless of
whether `i` and `j` lie inside the array bounds. -/
 theorem _root_.P2MLLL.t00ef6f00.h87
    (b : Matrix Int n m) (i j : Nat) (hij : i < j) :
    getArrayEntry (scaledCoeffRows b) i j = 0 := by
  unfold scaledCoeffRows
  exact _root_.P2MLLL.t00ef6f00.h35 n n _
    (fun i' j' hij' => _root_.P2MLLL.t00ef6f00.h58 n i' j') i j hij
open _root_.P2MLLL.t00ef6f00 renaming h87 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRows_above
open _root_.P2MLLL.t00ef6f00 renaming h87 → _p2mH87














end GramSchmidt.Int
open _root_.P2MLLL.t00ef6f00 renaming h87 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRows_above
open _root_.P2MLLL.t00ef6f00 renaming h87 → _p2mH87
open _root_.P2MLLL.t00ef6f00 renaming h88 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRows_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h88 → _p2mH88
open _root_.P2MLLL.t00ef6f00 renaming h89 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_diag_matches
open _root_.P2MLLL.t00ef6f00 renaming h89 → _p2mH89
open _root_.P2MLLL.t00ef6f00 renaming h90 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_lower_matches_target_column
open _root_.P2MLLL.t00ef6f00 renaming h90 → _p2mH90
open _root_.P2MLLL.t00ef6f00 renaming h91 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_lower_singular_after_step
open _root_.P2MLLL.t00ef6f00 renaming h91 → _p2mH91
open _root_.P2MLLL.t00ef6f00 renaming h92 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_lower_zero
open _root_.P2MLLL.t00ef6f00 renaming h92 → _p2mH92

end Hex
open _root_.P2MLLL.t00ef6f00 renaming h87 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRows_above
open _root_.P2MLLL.t00ef6f00 renaming h87 → _p2mH87
open _root_.P2MLLL.t00ef6f00 renaming h88 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRows_col_zero
open _root_.P2MLLL.t00ef6f00 renaming h88 → _p2mH88
open _root_.P2MLLL.t00ef6f00 renaming h89 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_diag_matches
open _root_.P2MLLL.t00ef6f00 renaming h89 → _p2mH89
open _root_.P2MLLL.t00ef6f00 renaming h90 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_lower_matches_target_column
open _root_.P2MLLL.t00ef6f00 renaming h90 → _p2mH90
open _root_.P2MLLL.t00ef6f00 renaming h91 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_lower_singular_after_step
open _root_.P2MLLL.t00ef6f00 renaming h91 → _p2mH91
open _root_.P2MLLL.t00ef6f00 renaming h92 → Hex.GramSchmidt.Int.scaledCoeffArrayLoop_lower_zero
open _root_.P2MLLL.t00ef6f00 renaming h92 → _p2mH92


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

set_option maxHeartbeats 1600000

namespace Hex
namespace GramSchmidt.Int
/-! # Prefix coefficient vector for integer row combinations -/

































/-! # Dot-product symmetry support -/

set_option maxRecDepth 8192
 theorem _root_.P2MLLL.t00ef6f00.h15 {n' : Nat} (xs : List (Fin n'))
    (u v : Vector Int n') (accU accV : Int) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind
open _root_.P2MLLL.t00ef6f00 renaming h15 → Hex.GramSchmidt.Int.foldl_dot_comm_int
open _root_.P2MLLL.t00ef6f00 renaming h15 → _p2mH15


set_option maxRecDepth 8192
/-- The dot product of integer vectors is commutative. -/
 theorem _root_.P2MLLL.t00ef6f00.h13 {n' : Nat} (u v : Vector Int n') :
    u.dotProduct v = v.dotProduct u := by
  simpa [Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using
    _root_.P2MLLL.t00ef6f00.h15 (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl
open _root_.P2MLLL.t00ef6f00 renaming h13 → Hex.GramSchmidt.Int.dot_comm_int
open _root_.P2MLLL.t00ef6f00 renaming h13 → _p2mH13


set_option maxRecDepth 8192
/-- The integer Gram matrix is symmetric: each entry equals the entry at the
swapped index. Consumed by the no-pivot Bareiss symmetry/transpose argument for
bordered minors of `gramMatrix b`. -/
 theorem _root_.P2MLLL.t00ef6f00.h16 (b : Matrix Int n m) (a c : Fin n) :
    (Matrix.gramMatrix b)[a][c] = (Matrix.gramMatrix b)[c][a] := by
  rw [Matrix.getElem_gramMatrix, Matrix.getElem_gramMatrix]
  exact _root_.P2MLLL.t00ef6f00.h13 _ _
open _root_.P2MLLL.t00ef6f00 renaming h16 → Hex.GramSchmidt.Int.gramMatrix_symm
open _root_.P2MLLL.t00ef6f00 renaming h16 → _p2mH16








set_option maxRecDepth 8192
/-- Singular dual of `scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix`,
phrased on the Bareiss-array path. When the no-pivot Bareiss pass over the
full Gram matrix records an early singular step before reaching column `j`,
the column-major array loop never writes the target column and the entry at
`(i, j)` below the diagonal is left at its initial zero. -/
 theorem _root_.P2MLLL.t00ef6f00.h20
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    getArrayEntry (scaledCoeffRows b) i.val j.val = 0 := by
  have h_target_sing :
      (Matrix.noPivotLoop (j.val - 0)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s := by
    simpa using h_sing
  have h_zero :=
    _root_.P2MLLL.t00ef6f00.h92
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (_root_.P2MLLL.t00ef6f00.h69 b) (by rfl)
      (_root_.P2MLLL.t00ef6f00.h66 b) (_root_.P2MLLL.t00ef6f00.h65 b)
      (_root_.P2MLLL.t00ef6f00.h86 n) (_root_.P2MLLL.t00ef6f00.h85 n)
      (by
        intro r c _hsc _hcr
        exact _root_.P2MLLL.t00ef6f00.h58 n r.val c.val)
      rfl
      n i j (Nat.zero_le _) hji
      (by have := i.isLt; omega) s h_target_sing
  show getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i.val j.val = 0
  exact h_zero
open _root_.P2MLLL.t00ef6f00 renaming h20 → Hex.GramSchmidt.Int.scaledCoeffRows_eq_zero_of_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h20 → _p2mH20


set_option maxRecDepth 8192
/-- Strict-lower non-singular Bareiss-side bridge: state-level form of
`scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix` extracted at the
`gramMatrix` matrix-level, before the bordered-minor/transpose closure. When
the no-pivot Bareiss pass over the full Gram matrix has not recorded a
singular step before reaching column `j`, the executable scaled-coefficient
array entry below the diagonal at `(i, j)` matches the matrix-level diagonal
of `noPivotLoop` at fuel `j` on `gramMatrix b`. -/
 theorem _root_.P2MLLL.t00ef6f00.h21
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    getArrayEntry (scaledCoeffRows b) i.val j.val =
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] := by
  have h_target_nonsing :
      (Matrix.noPivotLoop (j.val - 0)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
    simpa using h_nonsing
  have h_lower :=
    _root_.P2MLLL.t00ef6f00.h90
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (_root_.P2MLLL.t00ef6f00.h69 b) (by rfl)
      (_root_.P2MLLL.t00ef6f00.h66 b) (_root_.P2MLLL.t00ef6f00.h65 b)
      (_root_.P2MLLL.t00ef6f00.h86 n) (_root_.P2MLLL.t00ef6f00.h85 n)
      n i j (Nat.zero_le _) hji
      (by have := i.isLt; omega) h_target_nonsing
  show getArrayEntry
      (scaledCoeffArrayLoop n n
          { step := 0, matrix := gramRows b, coeffs := zeroRows n,
            prevPivot := 1 }).coeffs i.val j.val = _
  have h_step_eq : (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step = 0 := rfl
  have h_sub :
      j.val - (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step = j.val := by
    rw [h_step_eq]; omega
  rw [h_lower, h_sub]
open _root_.P2MLLL.t00ef6f00 renaming h21 → Hex.GramSchmidt.Int.scaledCoeffRows_lower_eq
open _root_.P2MLLL.t00ef6f00 renaming h21 → _p2mH21


set_option maxRecDepth 8192
/-- Diagonal non-singular Bareiss-side bridge. When the no-pivot Bareiss pass
over the full Gram matrix has not recorded a singular step before reaching
column `j`, the executable scaled-coefficient array entry on the diagonal at
`(j, j)` matches the matrix-level diagonal of `noPivotLoop` at fuel `j` on
`gramMatrix b`. The proof composes `scaledCoeffArrayLoop_diag_matches` at
fuel `n` with `Matrix.noPivotLoop_diag_of_le_step` plus
`noPivotLoop_step_eq_add_of_singularStep_none` to bridge between the
full-trajectory diagonal at `j` and the truncated-trajectory diagonal at the
same row. -/
 theorem _root_.P2MLLL.t00ef6f00.h18
    (b : Matrix Int n m) (j : Fin n)
    (h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    getArrayEntry (scaledCoeffRows b) j.val j.val =
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[j][j] := by
  let init : Matrix.BareissState Int n :=
    Matrix.noPivotInitialState (Matrix.gramMatrix b)
  let prefAtJ : Matrix.BareissState Int n := Matrix.noPivotLoop j.val init
  have h_step_j : prefAtJ.step = j.val := by
    have h_room : init.step + j.val + 1 ≤ n := by
      have := j.isLt
      simp [init, Matrix.noPivotInitialState]
      omega
    have h := _root_.P2MLLL.t00ef6f00.h126 j.val init rfl h_room h_nonsing
    simpa [prefAtJ, init, Matrix.noPivotInitialState] using h
  have h_factor :
      Matrix.noPivotLoop n init = Matrix.noPivotLoop (n - j.val) prefAtJ := by
    have h_add := Matrix.noPivotLoop_add j.val (n - j.val) init
    have h_split : j.val + (n - j.val) = n := by have := j.isLt; omega
    simpa [prefAtJ, h_split] using h_add
  have h_diag_bridge :
      (Matrix.noPivotLoop n init).matrix[j][j] = prefAtJ.matrix[j][j] := by
    rw [h_factor]
    have h_le : j.val ≤ prefAtJ.step := by rw [h_step_j]; exact Nat.le_refl _
    exact _root_.P2MLLL.t00ef6f00.h5 (n - j.val) prefAtJ j h_le
  have hdiag :=
    _root_.P2MLLL.t00ef6f00.h89
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := init)
      (by rfl) (_root_.P2MLLL.t00ef6f00.h69 b) (by rfl) (by rfl)
      (_root_.P2MLLL.t00ef6f00.h66 b) (_root_.P2MLLL.t00ef6f00.h65 b)
      (_root_.P2MLLL.t00ef6f00.h86 n) (_root_.P2MLLL.t00ef6f00.h85 n)
      (by
        intro k hks _hkn
        simp [init, Matrix.noPivotInitialState] at hks)
      (by
        intro k _hks _hkn
        exact _root_.P2MLLL.t00ef6f00.h58 n k k)
      n j (by
        left
        show j.val < (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + n
        simp [Matrix.noPivotInitialState, j.isLt])
  show getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs j.val j.val =
    prefAtJ.matrix[j][j]
  rcases hdiag with ⟨_h_sing_n, h_eq⟩ | ⟨s, h_sing_n, h_cases⟩
  · -- Non-singular full trajectory: bridge directly.
    rw [h_eq]; exact h_diag_bridge
  · rcases h_cases with ⟨hsj, h_zero⟩ | ⟨hjs, h_eq⟩
    · -- Sub-case `s ≤ j.val`: by monotonicity `j.val ≤ s`, so `s = j.val`; then
      -- the singular_inv invariant gives `(noPivotLoop n init).matrix[j][j] = 0`,
      -- which combined with `h_diag_bridge` shows `prefAtJ.matrix[j][j] = 0`.
      have h_mono :
          prefAtJ.step ≤ (Matrix.noPivotLoop (n - j.val) prefAtJ).step :=
        _root_.P2MLLL.t00ef6f00.h3 _ _
      have h_step_n_eq :
          (Matrix.noPivotLoop n init).step =
            (Matrix.noPivotLoop (n - j.val) prefAtJ).step :=
        congrArg Matrix.BareissState.step h_factor
      rcases noPivotLoop_singular_inv (n := n) n init rfl with h_none | ⟨k, h_k_sing, h_k_step, h_k_zero, _⟩
      · rw [h_sing_n] at h_none; nomatch h_none
      · have h_s_eq_k : s = k.val := by
          rw [h_k_sing] at h_sing_n
          injection h_sing_n with heq
          exact heq.symm
        have h_step_n_eq_s :
            (Matrix.noPivotLoop n init).step = s := by
          rw [h_k_step, h_s_eq_k]
        have h_j_le_s : j.val ≤ s := by
          have h_chain : prefAtJ.step ≤ (Matrix.noPivotLoop n init).step := by
            rw [h_step_n_eq]; exact h_mono
          rw [h_step_j, h_step_n_eq_s] at h_chain
          exact h_chain
        have h_s_eq_j : s = j.val := Nat.le_antisymm hsj h_j_le_s
        have h_idx_eq : k = j := by
          apply Fin.ext
          rw [← h_s_eq_k]; exact h_s_eq_j
        have h_matrix_n_jj :
            (Matrix.noPivotLoop n init).matrix[j][j] = 0 := by
          have h_lift := congrArg
            (fun (idx : Fin n) => (Matrix.noPivotLoop n init).matrix[idx][idx])
            h_idx_eq
          exact h_lift.symm.trans h_k_zero
        have h_prefAtJ_jj : prefAtJ.matrix[j][j] = 0 := by
          rw [← h_diag_bridge]; exact h_matrix_n_jj
        rw [h_zero, h_prefAtJ_jj]
    · -- Sub-case `j.val < s`: same bridge as the non-singular case.
      rw [h_eq]; exact h_diag_bridge
open _root_.P2MLLL.t00ef6f00 renaming h18 → Hex.GramSchmidt.Int.scaledCoeffRows_diag_eq_noPivotLoop_gramMatrix_of_no_singular
open _root_.P2MLLL.t00ef6f00 renaming h18 → _p2mH18


set_option maxRecDepth 8192
/-- Diagonal singular Bareiss-side bridge. When the no-pivot Bareiss pass
over the full Gram matrix records a singular step strictly before column `j`,
the executable scaled-coefficient array entry on the diagonal at `(j, j)` is
zero. The proof composes `scaledCoeffArrayLoop_diag_matches` at fuel `n` with
the persistence lemma `noPivotLoop_singularStep`. -/
 theorem _root_.P2MLLL.t00ef6f00.h19
    (b : Matrix Int n m) (j : Fin n)
    (s : Nat) (hsj : s < j.val)
    (h_sing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    getArrayEntry (scaledCoeffRows b) j.val j.val = 0 := by
  let init : Matrix.BareissState Int n :=
    Matrix.noPivotInitialState (Matrix.gramMatrix b)
  -- Lift singularity from prefix `j` to full `n` via `prefix_singular`.
  have h_persist_split :
      Matrix.noPivotLoop (j.val + (n - j.val)) init =
        Matrix.noPivotLoop n init := by
    have h_split : j.val + (n - j.val) = n := by have := j.isLt; omega
    rw [h_split]
  have h_sing_full' :
      (Matrix.noPivotLoop (j.val + (n - j.val)) init).singularStep = some s :=
    _root_.P2MLLL.t00ef6f00.h125 j.val (n - j.val) init rfl h_sing
  have h_sing_full : (Matrix.noPivotLoop n init).singularStep = some s := by
    rw [← h_persist_split]; exact h_sing_full'
  have hdiag :=
    _root_.P2MLLL.t00ef6f00.h89
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := init)
      (by rfl) (_root_.P2MLLL.t00ef6f00.h69 b) (by rfl) (by rfl)
      (_root_.P2MLLL.t00ef6f00.h66 b) (_root_.P2MLLL.t00ef6f00.h65 b)
      (_root_.P2MLLL.t00ef6f00.h86 n) (_root_.P2MLLL.t00ef6f00.h85 n)
      (by
        intro k hks _hkn
        simp [init, Matrix.noPivotInitialState] at hks)
      (by
        intro k _hks _hkn
        exact _root_.P2MLLL.t00ef6f00.h58 n k k)
      n j (by
        left
        show j.val < (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + n
        simp [Matrix.noPivotInitialState, j.isLt])
  show getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs j.val j.val = 0
  rcases hdiag with ⟨h_none, _⟩ | ⟨s', h_sing_n, h_cases⟩
  · rw [h_sing_full] at h_none; nomatch h_none
  · have h_s_eq : s' = s := by
      rw [h_sing_full] at h_sing_n
      injection h_sing_n with heq
      exact heq.symm
    have h_s'_le_j : s' ≤ j.val := by rw [h_s_eq]; omega
    rcases h_cases with ⟨_hsj', h_zero⟩ | ⟨hjs', _h_eq⟩
    · exact h_zero
    · -- j.val < s' contradicts s' ≤ j.val
      omega
open _root_.P2MLLL.t00ef6f00 renaming h19 → Hex.GramSchmidt.Int.scaledCoeffRows_diag_eq_zero_of_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h19 → _p2mH19


set_option maxRecDepth 8192
/-- On a non-singular initial Gram trajectory, the diagonal pivot at step `q`
is nonzero whenever `q + 1` iterations stay non-singular. The (`q + 1`)-th
iteration would otherwise record a singular step at `q`. -/
 theorem _root_.P2MLLL.t00ef6f00.h17
    (b : Matrix Int n m) (p q : Nat) (hq : q < p) (hpn : p < n)
    (h_nonsing :
      (Matrix.noPivotLoop p
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.noPivotLoop q
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
      (⟨q, Nat.lt_trans hq hpn⟩ : Fin n)][
      (⟨q, Nat.lt_trans hq hpn⟩ : Fin n)] ≠ 0 := by
  intro h_zero
  -- The (q+1)-prefix is also non-singular: split p = (q+1) + (p - q - 1).
  let state₀ : Matrix.BareissState Int n := Matrix.noPivotInitialState (Matrix.gramMatrix b)
  have h_split : p = (q + 1) + (p - q - 1) := by omega
  have h_prefix_succ_none :
      (Matrix.noPivotLoop (q + 1) state₀).singularStep = none := by
    apply _root_.P2MLLL.t00ef6f00.h124 (q + 1) (p - q - 1) state₀
      (by simp [state₀, Matrix.noPivotInitialState])
    rw [← h_split]; exact h_nonsing
  -- At step q (where step = q under non-singularity of q-prefix), the q-th
  -- diagonal is the pivot for the (q+1)-th iteration.
  have h_prefix_none :
      (Matrix.noPivotLoop q state₀).singularStep = none :=
    _root_.P2MLLL.t00ef6f00.h124 q 1 state₀
      (by simp [state₀, Matrix.noPivotInitialState])
      (by rw [show q + 1 = q + 1 from rfl]; exact h_prefix_succ_none)
  have hqn : q < n := Nat.lt_trans hq hpn
  have h_step_q :
      (Matrix.noPivotLoop q state₀).step = q :=
    _root_.P2MLLL.t00ef6f00.h12 b q (by omega) h_prefix_none
  -- The (q+1)-th iteration: starting from state with step = q, matrix[q][q] = 0,
  -- it records singularStep := some q.
  have hDone : (Matrix.noPivotLoop q state₀).step + 1 < n := by
    rw [h_step_q]; omega
  have hp_at_step :
      (Matrix.noPivotLoop q state₀).matrix[
        (Matrix.noPivotLoop q state₀).step][
        (Matrix.noPivotLoop q state₀).step] = 0 := by
    have h_idx_eq :
        (⟨(Matrix.noPivotLoop q state₀).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)
          = ⟨q, hqn⟩ := Fin.ext h_step_q
    have h_lift := congrArg
      (fun (idx : Fin n) =>
        (Matrix.noPivotLoop q state₀).matrix[idx][idx])
      h_idx_eq
    -- h_lift : M[⟨step, _⟩][⟨step, _⟩] = M[⟨q, _⟩][⟨q, _⟩]
    change
      (Matrix.noPivotLoop q state₀).matrix[
        (⟨(Matrix.noPivotLoop q state₀).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨(Matrix.noPivotLoop q state₀).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0
    exact h_lift.trans h_zero
  -- Now noPivotLoop applied for 1 more fuel from the q-prefix records a singular
  -- step at q. But that contradicts the (q+1)-prefix non-singularity.
  have h_one_more :
      Matrix.noPivotLoop 1 (Matrix.noPivotLoop q state₀) =
        { (Matrix.noPivotLoop q state₀) with
          singularStep := some (Matrix.noPivotLoop q state₀).step } :=
    Matrix.noPivotLoop_of_singular 0 _ hDone hp_at_step
  have h_q_plus_one :
      Matrix.noPivotLoop (q + 1) state₀ =
        Matrix.noPivotLoop 1 (Matrix.noPivotLoop q state₀) :=
    Matrix.noPivotLoop_add q 1 state₀
  rw [h_q_plus_one, h_one_more] at h_prefix_succ_none
  simp at h_prefix_succ_none
open _root_.P2MLLL.t00ef6f00 renaming h17 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_diag_ne_zero
open _root_.P2MLLL.t00ef6f00 renaming h17 → _p2mH17


set_option maxRecDepth 8192
/-- Algebraic exact-division step used by the σ-chain correction successor:
if the Bareiss update numerator is divisible by the previous pivot, the σ-body
quotient subtracts the corresponding Bareiss quotient from `pivot * gram`. -/
 theorem _root_.P2MLLL.t00ef6f00.h14
    (denom pivot gram entry row col : Int) (hdenom : denom ≠ 0)
    (hdiv : denom ∣ pivot * entry - row * col) :
    Matrix.exactDiv (pivot * (denom * gram - entry) + row * col) denom =
      pivot * gram - Matrix.exactDiv (pivot * entry - row * col) denom := by
  rcases hdiv with ⟨quot, hnum⟩
  have hquot :
      Matrix.exactDiv (pivot * entry - row * col) denom = quot := by
    refine _root_.Hex.GramSchmidt.Int.exactDiv_eq_of_eq_mul_right hdenom ?_
    rw [hnum]
    grind
  rw [hquot]
  refine _root_.Hex.GramSchmidt.Int.exactDiv_eq_of_eq_mul_right hdenom ?_
  have hrow : row * col = pivot * entry - denom * quot := by
    grind
  rw [hrow]
  grind
open _root_.P2MLLL.t00ef6f00 renaming h14 → Hex.GramSchmidt.Int.exactDiv_bareissCorrection_succ_algebra
open _root_.P2MLLL.t00ef6f00 renaming h14 → _p2mH14


set_option maxRecDepth 8192
/-- Successor step for the σ-chain/Bareiss correction invariant.  Once the
row reads in the σ-chain body have already been rewritten to a Bareiss
trajectory, one body application advances the closed correction term from the
current step to the next one.  The caller supplies the one-step Bareiss quotient
for the next matrix entry. -/
 theorem _root_.P2MLLL.t00ef6f00.h23
    (denom pivot gram entry row col nextEntry : Int)
    (hdenom : denom ≠ 0)
    (h_step_dvd : denom ∣ pivot * entry - row * col)
    (h_next :
      nextEntry = Matrix.exactDiv (pivot * entry - row * col) denom) :
    Matrix.exactDiv (pivot * (denom * gram - entry) + row * col) denom =
      pivot * gram - nextEntry := by
  rw [h_next]
  exact _root_.P2MLLL.t00ef6f00.h14
    denom pivot gram entry row col hdenom h_step_dvd
open _root_.P2MLLL.t00ef6f00 renaming h23 → Hex.GramSchmidt.Int.schurSigma_noPivotCorrection_succ
open _root_.P2MLLL.t00ef6f00 renaming h23 → _p2mH23


set_option maxRecDepth 8192
set_option maxHeartbeats 1600000 in
/-- The σ-chain Bareiss correction invariant.  At step `q < p_out` of the
σ-update fold for position `(a, p_out)`, the cumulative fold value equals
the algebraic closed form `matrix_q[q][q] * gram - matrix_(q+1)[a][p_out]`.
Proved by induction on `q`. -/
 theorem _root_.P2MLLL.t00ef6f00.h22
    {n m : Nat} (b : Matrix Int n m) (hquot : StepWitness b)
    (a p_out q : Nat) (hp_out_n : p_out < n) (han : a < n) (hpa : p_out ≤ a)
    (hq_lt_pout : q < p_out)
    (h_nonsing :
      (Matrix.noPivotLoop p_out
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (correspondence :
      ∀ l (hl : l ≤ q),
        getArrayEntry (scaledCoeffRowsSchur b) l l =
          (Matrix.noPivotLoop l
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
            (⟨l, Nat.lt_of_le_of_lt (Nat.le_trans hl (Nat.le_of_lt hq_lt_pout)) hp_out_n⟩
              : Fin n)][
            (⟨l, Nat.lt_of_le_of_lt (Nat.le_trans hl (Nat.le_of_lt hq_lt_pout)) hp_out_n⟩
              : Fin n)] ∧
        ∀ c (_hlc : l < c) (hcn : c < n),
          getArrayEntry (scaledCoeffRowsSchur b) c l =
            (Matrix.noPivotLoop l
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
              (⟨c, hcn⟩ : Fin n)][
              (⟨l, Nat.lt_of_le_of_lt (Nat.le_trans hl (Nat.le_of_lt hq_lt_pout)) hp_out_n⟩
                : Fin n)]) :
    (List.range' 1 q).foldl
        (fun σ p_iter =>
          Matrix.exactDiv
            (getArrayEntry (scaledCoeffRowsSchur b) p_iter p_iter * σ +
              getArrayEntry (scaledCoeffRowsSchur b) a p_iter *
              getArrayEntry (scaledCoeffRowsSchur b) p_out p_iter)
            (getArrayEntry (scaledCoeffRowsSchur b) (p_iter - 1) (p_iter - 1)))
        (getArrayEntry (scaledCoeffRowsSchur b) a 0 *
          getArrayEntry (scaledCoeffRowsSchur b) p_out 0) =
      (Matrix.noPivotLoop q
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
        (⟨q, Nat.lt_trans hq_lt_pout hp_out_n⟩ : Fin n)][
        (⟨q, Nat.lt_trans hq_lt_pout hp_out_n⟩ : Fin n)] *
        (Matrix.gramMatrix b)[(⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)] -
      (Matrix.noPivotLoop (q + 1)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
        (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)] := by
  induction q with
  | zero =>
    -- Empty fold; reduce to the q = 0 algebraic identity via the gramMatrix
    -- entries supplied by `correspondence` at `l = 0`.
    have hp_out_pos : 0 < p_out := hq_lt_pout
    have h0a : 0 < a := Nat.lt_of_lt_of_le hp_out_pos hpa
    have ih0 := correspondence 0 (Nat.le_refl 0)
    have h_rows_a0 :
        getArrayEntry (scaledCoeffRowsSchur b) a 0 =
          (Matrix.gramMatrix b)[(⟨a, han⟩ : Fin n)][
            (⟨0, Nat.lt_trans hp_out_pos hp_out_n⟩ : Fin n)] := by
      simpa [Matrix.noPivotLoop_zero_fuel, Matrix.noPivotInitialState] using
        ih0.2 a h0a han
    have h_rows_p0 :
        getArrayEntry (scaledCoeffRowsSchur b) p_out 0 =
          (Matrix.gramMatrix b)[(⟨p_out, hp_out_n⟩ : Fin n)][
            (⟨0, Nat.lt_trans hp_out_pos hp_out_n⟩ : Fin n)] := by
      simpa [Matrix.noPivotLoop_zero_fuel, Matrix.noPivotInitialState] using
        ih0.2 p_out hp_out_pos hp_out_n
    have h_sym_p0 :
        (Matrix.gramMatrix b)[(⟨p_out, hp_out_n⟩ : Fin n)][
            (⟨0, Nat.lt_trans hp_out_pos hp_out_n⟩ : Fin n)] =
          (Matrix.gramMatrix b)[(⟨0, Nat.lt_trans hp_out_pos hp_out_n⟩ : Fin n)][
            (⟨p_out, hp_out_n⟩ : Fin n)] :=
      _root_.P2MLLL.t00ef6f00.h16 (b := b) _ _
    have hDone :
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + 1 < n := by
      simp [Matrix.noPivotInitialState]; omega
    have hpivot :
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step][
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step] ≠ 0 := by
      have key :=
        _root_.P2MLLL.t00ef6f00.h17
          (b := b) p_out 0 hp_out_pos hp_out_n h_nonsing
      simp only [Matrix.noPivotInitialState]
      exact key
    rw [Matrix.noPivotLoop_of_regular 0
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) hDone hpivot]
    simp [Matrix.noPivotLoop_zero_fuel, Matrix.noPivotInitialState]
    have hofFn : ∀ (f : Fin n → Fin n → Int) (r : Fin n) (jj : Nat) (hjj : jj < n),
        ((Matrix.ofFn f).getRow r)[jj] = f r ⟨jj, hjj⟩ := by
      intro f r jj hjj
      rw [← Hex.Matrix.getElem_eq_getRow]
      exact Hex.Matrix.getElem_ofFn f r ⟨jj, hjj⟩
    simp [_root_.P2MLLL.t00ef6f00.h8, Matrix.exactDiv, HexArith.Int.exactDiv,
      hofFn, h0a, hp_out_pos,
      h_rows_a0, h_rows_p0]
    grind
  | succ q' ih =>
    -- Extend the fold by one iteration; rewrite the body via correspondence,
    -- apply the IH, then close via `schurSigma_noPivotCorrection_succ`.
    let state₀ : Matrix.BareissState Int n :=
      Matrix.noPivotInitialState (Matrix.gramMatrix b)
    have h_init_none : state₀.singularStep = none := by
      simp [state₀, Matrix.noPivotInitialState]
    have hq'_lt : q' < p_out := Nat.lt_of_succ_lt hq_lt_pout
    have hq'_succ_lt : q' + 1 < p_out := hq_lt_pout
    have hq'_n : q' < n := Nat.lt_trans hq'_lt hp_out_n
    have hq'_succ_n : q' + 1 < n := Nat.lt_trans hq'_succ_lt hp_out_n
    have hp_a_lt : q' + 1 < a := Nat.lt_of_lt_of_le hq'_succ_lt hpa
    -- (loop (q'+1)) and (loop q') are both non-singular prefixes of (loop p_out).
    have h_prefix_q'_succ_none :
        (Matrix.noPivotLoop (q' + 1) state₀).singularStep = none := by
      apply _root_.P2MLLL.t00ef6f00.h124 (q' + 1) (p_out - (q' + 1)) state₀
        h_init_none
      have h_eq : (q' + 1) + (p_out - (q' + 1)) = p_out := by omega
      rw [h_eq]; exact h_nonsing
    have h_prefix_q'_none :
        (Matrix.noPivotLoop q' state₀).singularStep = none := by
      apply _root_.P2MLLL.t00ef6f00.h124 q' (p_out - q') state₀ h_init_none
      have h_eq : q' + (p_out - q') = p_out := by omega
      rw [h_eq]; exact h_nonsing
    -- step matches fuel under non-singular prefix.
    have h_step_q' : (Matrix.noPivotLoop q' state₀).step = q' :=
      _root_.P2MLLL.t00ef6f00.h12 b q' (by omega) h_prefix_q'_none
    have h_step_q'_succ : (Matrix.noPivotLoop (q' + 1) state₀).step = q' + 1 :=
      _root_.P2MLLL.t00ef6f00.h12 b (q' + 1) (by omega)
        h_prefix_q'_succ_none
    -- Apply the inductive hypothesis at q'.
    have ih_eq :=
      ih hq'_lt (fun l hl => correspondence l (Nat.le_succ_of_le hl))
    -- Extract correspondence values needed for the new body at p_iter = q' + 1.
    have corr_q' := correspondence q' (Nat.le_succ q')
    have corr_q'_succ := correspondence (q' + 1) (Nat.le_refl (q' + 1))
    -- diagonal at q' (the denominator)
    have h_rows_q'_diag :
        getArrayEntry (scaledCoeffRowsSchur b) q' q' =
          (Matrix.noPivotLoop q' state₀).matrix[
            (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] := corr_q'.1
    -- diagonal at q'+1 (the pivot)
    have h_rows_q'_succ_diag :
        getArrayEntry (scaledCoeffRowsSchur b) (q' + 1) (q' + 1) =
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
            (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
            (⟨q' + 1, hq'_succ_n⟩ : Fin n)] := corr_q'_succ.1
    -- entries at row a and row p_out, column q' + 1
    have h_rows_a_q'_succ :
        getArrayEntry (scaledCoeffRowsSchur b) a (q' + 1) =
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
            (⟨a, han⟩ : Fin n)][
            (⟨q' + 1, hq'_succ_n⟩ : Fin n)] :=
      corr_q'_succ.2 a hp_a_lt han
    have h_rows_p_q'_succ :
        getArrayEntry (scaledCoeffRowsSchur b) p_out (q' + 1) =
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
            (⟨p_out, hp_out_n⟩ : Fin n)][
            (⟨q' + 1, hq'_succ_n⟩ : Fin n)] :=
      corr_q'_succ.2 p_out hq'_succ_lt hp_out_n
    -- prevPivot at fuel q'+1: this is matrix_q'[q'][q'].
    have h_prevPivot_q'_succ :
        (Matrix.noPivotLoop (q' + 1) state₀).prevPivot =
          (Matrix.noPivotLoop q' state₀).matrix[
            (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] := by
      have h_add : Matrix.noPivotLoop (q' + 1) state₀ =
          Matrix.noPivotLoop 1 (Matrix.noPivotLoop q' state₀) :=
        Matrix.noPivotLoop_add q' 1 state₀
      have hDone :
          (Matrix.noPivotLoop q' state₀).step + 1 < n := by
        rw [h_step_q']; exact hq'_succ_n
      have h_idx_eq :
          (⟨(Matrix.noPivotLoop q' state₀).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n) = (⟨q', hq'_n⟩ : Fin n) :=
        Fin.ext h_step_q'
      have h_diag_at_q' :=
        _root_.P2MLLL.t00ef6f00.h17 b (q' + 1) q'
          (Nat.lt_succ_self q') hq'_succ_n h_prefix_q'_succ_none
      have h_eq_diag :
          (Matrix.noPivotLoop q' state₀).matrix[
              (⟨(Matrix.noPivotLoop q' state₀).step,
                  Nat.lt_of_succ_lt hDone⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop q' state₀).step,
                  Nat.lt_of_succ_lt hDone⟩ : Fin n)] =
            (Matrix.noPivotLoop q' state₀).matrix[
              (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] :=
        congrArg
          (fun (i : Fin n) => (Matrix.noPivotLoop q' state₀).matrix[i][i]) h_idx_eq
      have h_diag_at_step :
          (Matrix.noPivotLoop q' state₀).matrix[
              (⟨(Matrix.noPivotLoop q' state₀).step,
                  Nat.lt_of_succ_lt hDone⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop q' state₀).step,
                  Nat.lt_of_succ_lt hDone⟩ : Fin n)] ≠ 0 :=
        h_eq_diag ▸ h_diag_at_q'
      rw [h_add, Matrix.noPivotLoop_of_regular 0 _ hDone h_diag_at_step,
        Matrix.noPivotLoop_zero_fuel]
      -- The `noPivotLoop_of_regular` rewrite makes the goal:
      --   matrix[⟨step, ⋯⟩][⟨step, ⋯⟩] = matrix[⟨q', hq'_n⟩][⟨q', hq'_n⟩]
      -- which we close by the index equality.
      exact congrArg
        (fun (i : Fin n) =>
          (Matrix.noPivotLoop q' state₀).matrix[i][i]) h_idx_eq
    -- Bareiss step at fuel q'+1: matrix_(q'+2)[a][p_out] = exactDiv of the
    -- standard Bareiss numerator by prevPivot.
    have h_step_a_p :
        (Matrix.noPivotLoop (q' + 1 + 1) state₀).matrix[
            (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)] =
          Matrix.exactDiv
            ((Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
                (⟨q' + 1, hq'_succ_n⟩ : Fin n)] *
              (Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)] -
              (Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨a, han⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)] *
              (Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨q' + 1, hq'_succ_n⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)])
            ((Matrix.noPivotLoop (q' + 1) state₀).prevPivot) := by
      have h_add : Matrix.noPivotLoop (q' + 1 + 1) state₀ =
          Matrix.noPivotLoop 1 (Matrix.noPivotLoop (q' + 1) state₀) :=
        Matrix.noPivotLoop_add (q' + 1) 1 state₀
      rw [h_add]
      have hDone : (Matrix.noPivotLoop (q' + 1) state₀).step + 1 < n := by
        rw [h_step_q'_succ]; omega
      have hp :
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                Nat.lt_of_succ_lt hDone⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                Nat.lt_of_succ_lt hDone⟩ : Fin n)] ≠ 0 := by
        have h_diag := _root_.P2MLLL.t00ef6f00.h17 b p_out (q' + 1)
          hq'_succ_lt hp_out_n h_nonsing
        have h_idx :
            (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)
              = (⟨q' + 1, hq'_succ_n⟩ : Fin n) := Fin.ext h_step_q'_succ
        have h_eq :
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                    Nat.lt_of_succ_lt hDone⟩ : Fin n)][
                (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                    Nat.lt_of_succ_lt hDone⟩ : Fin n)] =
              (Matrix.noPivotLoop (q' + 1) state₀).matrix[
                (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
                (⟨q' + 1, hq'_succ_n⟩ : Fin n)] :=
          congrArg
            (fun (i : Fin n) =>
              (Matrix.noPivotLoop (q' + 1) state₀).matrix[i][i]) h_idx
        exact h_eq ▸ h_diag
      rw [Matrix.noPivotLoop_of_regular 0 _ hDone hp,
        Matrix.noPivotLoop_zero_fuel]
      have ha : (Matrix.noPivotLoop (q' + 1) state₀).step < a := by
        rw [h_step_q'_succ]; exact hp_a_lt
      have hpo : (Matrix.noPivotLoop (q' + 1) state₀).step < p_out := by
        rw [h_step_q'_succ]; exact hq'_succ_lt
      rw [Matrix.stepMatrix_update_eq (Matrix.noPivotLoop (q' + 1) state₀).matrix
        (Matrix.noPivotLoop (q' + 1) state₀).step _
        (Matrix.noPivotLoop (q' + 1) state₀).prevPivot
        (⟨a, han⟩ : Fin n) (⟨p_out, hp_out_n⟩ : Fin n) ha hpo]
      -- The remaining goal is to identify the unfolded `colK = ⟨step, _⟩`
      -- (and similarly `rowK`) with `⟨q'+1, hq'_succ_n⟩`. Substitute via the
      -- step-equality, then close by reflexivity (Fin proofs are irrelevant).
      simp only [h_step_q'_succ]
      rfl
    -- Symmetry of matrix_(q'+1) at (q'+1, p_out).
    -- Built by application (not by re-elaborating the written-out nested-getElem
    -- type, which whnf-reduces the `noPivotLoop` term and is very slow).
    have h_sym_pivot_row :=
      _root_.P2MLLL.t00ef6f00.h123 (q' + 1) state₀
        (fun x y _ _ => by
          simp only [state₀, Matrix.noPivotInitialState]
          exact _root_.P2MLLL.t00ef6f00.h16 (b := b) x y)
        (⟨q' + 1, hq'_succ_n⟩ : Fin n) (⟨p_out, hp_out_n⟩ : Fin n)
        (by rw [h_step_q'_succ]; exact Nat.le_refl _)
        (by rw [h_step_q'_succ]; exact Nat.le_of_lt hq'_succ_lt)
    -- Matrix-level Bareiss divisibility at fuel q'+1: prevPivot ∣ numerator.
    have hpivot_q'_succ :
        (Matrix.noPivotLoop (q' + 1) state₀).matrix[
          (Matrix.noPivotLoop (q' + 1) state₀).step][
          (Matrix.noPivotLoop (q' + 1) state₀).step] ≠ 0 := by
      have h_diag_ne :=
        _root_.P2MLLL.t00ef6f00.h17 b p_out (q' + 1)
          hq'_succ_lt hp_out_n h_nonsing
      have h_step_lt_n :
          (Matrix.noPivotLoop (q' + 1) state₀).step < n := by
        rw [h_step_q'_succ]; exact hq'_succ_n
      have h_idx :
          (⟨(Matrix.noPivotLoop (q' + 1) state₀).step, h_step_lt_n⟩ : Fin n)
            = (⟨q' + 1, hq'_succ_n⟩ : Fin n) := Fin.ext h_step_q'_succ
      have h_eq :
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                  h_step_lt_n⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step,
                  h_step_lt_n⟩ : Fin n)] =
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)] :=
        congrArg
          (fun (i : Fin n) =>
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[i][i]) h_idx
      exact h_eq ▸ h_diag_ne
    have h_step_dvd_raw :=
      _root_.P2MLLL.t00ef6f00.h111 b hquot (q' + 1)
        h_prefix_q'_succ_none
        (by rw [h_step_q'_succ]; omega)
        hpivot_q'_succ
        (⟨a, han⟩ : Fin n) (⟨p_out, hp_out_n⟩ : Fin n)
        (by rw [h_step_q'_succ]; exact hp_a_lt)
    -- Identify the `k` index in `h_step_dvd_raw` with `q'+1`.
    have h_step_dvd :
        (Matrix.noPivotLoop q' state₀).matrix[
            (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] ∣
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)] *
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)] -
          (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨a, han⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)] *
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨p_out, hp_out_n⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)] := by
      rw [← h_prevPivot_q'_succ, ← h_sym_pivot_row]
      -- Unfold the `let state, let k` in h_step_dvd_raw to get a normalized form.
      simp only at h_step_dvd_raw
      -- Now apply congrArg to identify the matrix entries with `⟨step, _⟩` =
      -- `⟨q' + 1, hq'_succ_n⟩` indices.
      have h_kk :
          ∀ (h_lt : (Matrix.noPivotLoop (q' + 1) state₀).step < n),
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step, h_lt⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step, h_lt⟩ : Fin n)] =
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)] := fun _ =>
        congrArg
          (fun (i : Fin n) =>
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[i][i])
          (Fin.ext h_step_q'_succ)
      have h_ak :
          ∀ (h_lt : (Matrix.noPivotLoop (q' + 1) state₀).step < n),
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨a, han⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step, h_lt⟩ : Fin n)] =
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨a, han⟩ : Fin n)][
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)] := fun _ =>
        congrArg
          (fun (i : Fin n) =>
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨a, han⟩ : Fin n)][i])
          (Fin.ext h_step_q'_succ)
      have h_kp :
          ∀ (h_lt : (Matrix.noPivotLoop (q' + 1) state₀).step < n),
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨(Matrix.noPivotLoop (q' + 1) state₀).step, h_lt⟩ : Fin n)][
              (⟨p_out, hp_out_n⟩ : Fin n)] =
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[
              (⟨q' + 1, hq'_succ_n⟩ : Fin n)][
              (⟨p_out, hp_out_n⟩ : Fin n)] := fun _ =>
        congrArg
          (fun (i : Fin n) =>
            (Matrix.noPivotLoop (q' + 1) state₀).matrix[i][
              (⟨p_out, hp_out_n⟩ : Fin n)])
          (Fin.ext h_step_q'_succ)
      rw [h_kk _, h_ak _, h_kp _] at h_step_dvd_raw
      exact h_step_dvd_raw
    -- nonzero denom
    have hdenom_ne :
        (Matrix.noPivotLoop q' state₀).matrix[
          (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] ≠ 0 :=
      _root_.P2MLLL.t00ef6f00.h17 b (q' + 1) q'
        (Nat.lt_succ_self q') hq'_succ_n h_prefix_q'_succ_none
    -- Now expand the fold: range' 1 (q' + 1) = range' 1 q' ++ [q' + 1].
    have h_concat :
        List.range' 1 (q' + 1) = List.range' 1 q' ++ [q' + 1] := by
      have := List.range'_concat (s := 1) (n := q') (step := 1)
      simpa [Nat.add_comm 1 q'] using this
    rw [h_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.add_sub_cancel]
    rw [ih_eq, h_rows_q'_diag, h_rows_q'_succ_diag, h_rows_a_q'_succ,
      h_rows_p_q'_succ]
    -- Close via the succ algebraic helper.
    exact _root_.P2MLLL.t00ef6f00.h23
      ((Matrix.noPivotLoop q' state₀).matrix[
          (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)])
      ((Matrix.noPivotLoop (q' + 1) state₀).matrix[
          (⟨q' + 1, hq'_succ_n⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)])
      ((Matrix.gramMatrix b)[(⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)])
      ((Matrix.noPivotLoop (q' + 1) state₀).matrix[
          (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)])
      ((Matrix.noPivotLoop (q' + 1) state₀).matrix[
          (⟨a, han⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)])
      ((Matrix.noPivotLoop (q' + 1) state₀).matrix[
          (⟨p_out, hp_out_n⟩ : Fin n)][(⟨q' + 1, hq'_succ_n⟩ : Fin n)])
      ((Matrix.noPivotLoop (q' + 1 + 1) state₀).matrix[
          (⟨a, han⟩ : Fin n)][(⟨p_out, hp_out_n⟩ : Fin n)])
      hdenom_ne h_step_dvd
      (by rw [h_step_a_p, h_prevPivot_q'_succ, h_sym_pivot_row])
open _root_.P2MLLL.t00ef6f00 renaming h22 → Hex.GramSchmidt.Int.schurSigma_foldl_eq
open _root_.P2MLLL.t00ef6f00 renaming h22 → _p2mH22


set_option maxRecDepth 8192
/-- Mathlib-free non-singular Schur ≡ Bareiss correspondence at a single
column.  When the no-pivot Bareiss pass over the full Gram matrix reaches
column `q` without recording a singular step, the diagonal slot and every
below-column entry of the integral Schur kernel match the corresponding
`noPivotLoop`/Bareiss matrix at fuel `q`.

Proved by strong induction on `q`. The base case `q = 0` reduces to the
column-zero boundary of the Schur kernel together with `noPivotLoop` at
zero fuel returning the initial Gram state. The step case `q' + 1` rewrites
the Schur recurrence `rows[c][q' + 1] = rows[q'][q'] · gram[c][q' + 1] -
schurSigma rows c (q' + 1)` and discharges the σ-chain via
`schurSigma_foldl_eq` at `p_out = q' + 1`, fed with the
σ-fold correspondence assembled from the strong inductive hypothesis. -/
theorem _root_.P2MLLL.t00ef6f00.h0
    {n m : Nat} (b : Matrix Int n m) (hquot : StepWitness b)
    (q : Nat) (hqn : q < n)
    (h_nonsing :
      (Matrix.noPivotLoop q
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (getArrayEntry (scaledCoeffRowsSchur b) q q =
      (Matrix.noPivotLoop q
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
        (⟨q, hqn⟩ : Fin n)][(⟨q, hqn⟩ : Fin n)]) ∧
    (∀ c (_hqc : q < c) (hcn : c < n),
      getArrayEntry (scaledCoeffRowsSchur b) c q =
        (Matrix.noPivotLoop q
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (⟨c, hcn⟩ : Fin n)][(⟨q, hqn⟩ : Fin n)]) := by
  revert hqn h_nonsing
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro hqn h_nonsing
    match q, hqn, h_nonsing, ih with
    | 0, hqn, _, _ =>
      refine ⟨?_, ?_⟩
      · rw [_root_.P2MLLL.t00ef6f00.h121,
          Matrix.noPivotLoop_zero_fuel]
        exact _root_.P2MLLL.t00ef6f00.h34 b ⟨0, hqn⟩ ⟨0, hqn⟩
      · intro c _hqc hcn
        rw [_root_.P2MLLL.t00ef6f00.h121,
          Matrix.noPivotLoop_zero_fuel]
        exact _root_.P2MLLL.t00ef6f00.h34 b ⟨c, hcn⟩ ⟨0, hqn⟩
    | q' + 1, hqn, h_nonsing, ih =>
      have hq'_lt_succ : q' < q' + 1 := Nat.lt_succ_self q'
      have hq'_n : q' < n := Nat.lt_of_succ_lt hqn
      have prefix_none : ∀ (l : Nat), l ≤ q' + 1 →
          (Matrix.noPivotLoop l
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
        intro l hl
        apply _root_.P2MLLL.t00ef6f00.h124 l (q' + 1 - l)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))
          (by simp [Matrix.noPivotInitialState])
        have h_eq : l + (q' + 1 - l) = q' + 1 := by omega
        rw [h_eq]
        exact h_nonsing
      have correspondence :
          ∀ (l : Nat) (hl : l ≤ q'),
            getArrayEntry (scaledCoeffRowsSchur b) l l =
              (Matrix.noPivotLoop l
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
                (⟨l, Nat.lt_of_le_of_lt
                      (Nat.le_trans hl (Nat.le_of_lt hq'_lt_succ)) hqn⟩
                  : Fin n)][
                (⟨l, Nat.lt_of_le_of_lt
                      (Nat.le_trans hl (Nat.le_of_lt hq'_lt_succ)) hqn⟩
                  : Fin n)] ∧
            ∀ c (_hlc : l < c) (hcn : c < n),
              getArrayEntry (scaledCoeffRowsSchur b) c l =
                (Matrix.noPivotLoop l
                    (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
                  (⟨c, hcn⟩ : Fin n)][
                  (⟨l, Nat.lt_of_le_of_lt
                        (Nat.le_trans hl (Nat.le_of_lt hq'_lt_succ)) hqn⟩
                    : Fin n)] := by
        intro l hl
        have hl_lt : l < q' + 1 := Nat.lt_succ_of_le hl
        have hl_n : l < n :=
          Nat.lt_of_le_of_lt (Nat.le_trans hl (Nat.le_of_lt hq'_lt_succ)) hqn
        have h_l_none := prefix_none l (Nat.le_of_lt hl_lt)
        exact ih l hl_lt hl_n h_l_none
      have ih_diag := (correspondence q' (Nat.le_refl q')).1
      have h_sigma_closed : ∀ (a : Nat) (han : a < n) (hpa : q' + 1 ≤ a),
          schurSigma (scaledCoeffRowsSchur b) a (q' + 1) =
            (Matrix.noPivotLoop q'
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
              (⟨q', hq'_n⟩ : Fin n)][(⟨q', hq'_n⟩ : Fin n)] *
              (Matrix.gramMatrix b)[(⟨a, han⟩ : Fin n)][
                (⟨q' + 1, hqn⟩ : Fin n)] -
            (Matrix.noPivotLoop (q' + 1)
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
              (⟨a, han⟩ : Fin n)][(⟨q' + 1, hqn⟩ : Fin n)] := by
        intro a han hpa
        have h_fold := _root_.P2MLLL.t00ef6f00.h22 b hquot a (q' + 1) q'
          hqn han hpa hq'_lt_succ h_nonsing correspondence
        show (Id.run do
              let mut sigma :=
                getArrayEntry (scaledCoeffRowsSchur b) a 0 *
                getArrayEntry (scaledCoeffRowsSchur b) (q' + 1) 0
              for p in [1:q' + 1] do
                sigma :=
                  Matrix.exactDiv
                    (getArrayEntry (scaledCoeffRowsSchur b) p p * sigma +
                      getArrayEntry (scaledCoeffRowsSchur b) a p *
                      getArrayEntry (scaledCoeffRowsSchur b) (q' + 1) p)
                    (getArrayEntry (scaledCoeffRowsSchur b) (p - 1) (p - 1))
              return sigma) = _
        simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
        exact h_fold
      refine ⟨?_, ?_⟩
      · rw [_root_.P2MLLL.t00ef6f00.h122 b (q' + 1)
          (q' + 1) (Nat.le_refl _) hqn]
        show schurScaledCoeffEntry (scaledCoeffRowsSchur b) (gramRows b) (q' + 1)
            (q' + 1) = _
        unfold schurScaledCoeffEntry
        rw [if_neg (Nat.succ_ne_zero q')]
        simp only [Nat.add_sub_cancel]
        rw [ih_diag,
          show getArrayEntry (gramRows b) (q' + 1) (q' + 1) =
              (Matrix.gramMatrix b)[(⟨q' + 1, hqn⟩ : Fin n)][
                (⟨q' + 1, hqn⟩ : Fin n)] from
            _root_.P2MLLL.t00ef6f00.h34 b ⟨q' + 1, hqn⟩ ⟨q' + 1, hqn⟩,
          h_sigma_closed (q' + 1) hqn (Nat.le_refl _)]
        grind
      · intro c hqc hcn
        have h_pa : q' + 1 ≤ c := Nat.le_of_lt hqc
        rw [_root_.P2MLLL.t00ef6f00.h122 b c (q' + 1)
          h_pa hcn]
        show schurScaledCoeffEntry (scaledCoeffRowsSchur b) (gramRows b) c (q' + 1) = _
        unfold schurScaledCoeffEntry
        rw [if_neg (Nat.succ_ne_zero q')]
        simp only [Nat.add_sub_cancel]
        rw [ih_diag,
          show getArrayEntry (gramRows b) c (q' + 1) =
              (Matrix.gramMatrix b)[(⟨c, hcn⟩ : Fin n)][
                (⟨q' + 1, hqn⟩ : Fin n)] from
            _root_.P2MLLL.t00ef6f00.h34 b ⟨c, hcn⟩ ⟨q' + 1, hqn⟩,
          h_sigma_closed c hcn h_pa]
        grind
open _root_.P2MLLL.t00ef6f00 renaming h0 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing
open _root_.P2MLLL.t00ef6f00 renaming h0 → _p2mH0


set_option maxRecDepth 8192
/-- Singular cascade at the Schur kernel. If the no-pivot Bareiss pass over
the full Gram matrix records an early singular step at column `s < j`, every
Schur-kernel entry in the column-`j`, weak-lower triangle (`j ≤ i`) vanishes.

The row-`s` column is cleared by combining the non-singular Schur≡Bareiss
correspondence at fuel `s`
(`getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing`) with the
column-zero structural lemma at the singular step
(`principalSubmatrix_gram_zero_pivot_column_zero`). Strong
induction on `j' ∈ (s, j]` then propagates the zeros via the Schur recurrence
`rows[i'][j'] = rows[j'-1][j'-1] · gram[i'][j'] - schurSigma i' j'`. The
diagonal factor `rows[j'-1][j'-1]` is zero by the row-`s` lemma when
`j' = s + 1` and by the cascade IH otherwise. The σ-fold collapses to zero
by sub-induction on the iteration count: the killing iteration `p = s`
makes all three relevant Schur entries zero (`rows[s][s] = 0` and
`rows[c][s] = 0` for `c ≥ s + 1`), so the σ-body `exactDiv` of zero by the
prev-pivot returns zero; subsequent iterations preserve zero via the outer
IH at columns `(s, j')`. The proof does not transitively cite
`getArrayEntry_scaledCoeffRowsSchur_eq` (the residual gap at line 6463). -/
theorem _root_.P2MLLL.t00ef6f00.h1
    {n m : Nat} (b : Matrix Int n m) (hquot : StepWitness b)
    (i j : Nat) (hi : i < n) (hji : j ≤ i)
    (s : Nat) (hsj : s < j)
    (h_sing : (Matrix.noPivotLoop j
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    getArrayEntry (scaledCoeffRowsSchur b) i j = 0 := by
  have hjn : j < n := Nat.lt_of_le_of_lt hji hi
  have hsn : s < n := Nat.lt_trans hsj hjn
  have hs_succ_le_n : s + 1 ≤ n := hsn
  obtain ⟨h_s_prefix_none, _h_s_step, h_s_diag_zero⟩ :=
    _root_.P2MLLL.t00ef6f00.h113 (Matrix.gramMatrix b) j s hs_succ_le_n h_sing
  have h_corr_at_s :=
    _root_.P2MLLL.t00ef6f00.h0 b hquot s hsn h_s_prefix_none
  -- Row-`s` is zero across the lower triangle (including the diagonal).
  have h_row_s_zero : ∀ (c : Nat), c < n → s ≤ c →
      getArrayEntry (scaledCoeffRowsSchur b) c s = 0 := by
    intro c hcn hcs
    by_cases hcs_eq : c = s
    · subst hcs_eq
      rw [h_corr_at_s.1]
      exact h_s_diag_zero
    · have hc_gt : s < c := Nat.lt_of_le_of_ne hcs (Ne.symm hcs_eq)
      have hs_succ_lt_n : s + 1 < n := Nat.lt_of_le_of_lt hc_gt hcn
      rw [h_corr_at_s.2 c hc_gt hcn]
      exact _root_.P2MLLL.t00ef6f00.h114
        b s hs_succ_lt_n hquot h_s_prefix_none h_s_diag_zero ⟨c, hcn⟩ hc_gt
  -- Strong induction on `j'` ∈ (s, j].
  suffices h_cascade : ∀ (j' : Nat), j' ≤ j → s < j' →
      ∀ (i' : Nat), j' ≤ i' → i' < n →
        getArrayEntry (scaledCoeffRowsSchur b) i' j' = 0 from
    h_cascade j (Nat.le_refl j) hsj i hji hi
  intro j' hj'j hsj' i' hj'i' hi'n
  revert hj'j hsj' i' hj'i' hi'n
  induction j' using Nat.strongRecOn with
  | ind j' ih =>
    intro hj'j hsj' i' hj'i' hi'n
    have hj'_pos : 0 < j' := Nat.lt_of_le_of_lt (Nat.zero_le _) hsj'
    have hj'n : j' < n := Nat.lt_of_le_of_lt hj'j hjn
    -- Apply the Schur recurrence at `(i', j')`.
    rw [_root_.P2MLLL.t00ef6f00.h122 b i' j' hj'i' hi'n]
    show schurScaledCoeffEntry (scaledCoeffRowsSchur b) (gramRows b) i' j' = 0
    unfold schurScaledCoeffEntry
    rw [if_neg (Nat.ne_of_gt hj'_pos)]
    -- Diagonal factor at `(j' - 1, j' - 1)` is zero.
    have h_diag_zero :
        getArrayEntry (scaledCoeffRowsSchur b) (j' - 1) (j' - 1) = 0 := by
      have hj'_sub_one_lt_n : j' - 1 < n := by omega
      by_cases hj'_eq_s : j' - 1 = s
      · rw [hj'_eq_s]
        exact h_row_s_zero s hsn (Nat.le_refl s)
      · have hj'_gt : s < j' - 1 := by omega
        have hj'_sub_one_lt_j' : j' - 1 < j' := by omega
        have hj'_sub_one_le_j : j' - 1 ≤ j := by omega
        exact ih (j' - 1) hj'_sub_one_lt_j' hj'_sub_one_le_j hj'_gt
          (j' - 1) (Nat.le_refl _) hj'_sub_one_lt_n
    -- σ-fold value at `(i', j')` is zero, by sub-induction on the iteration prefix.
    have h_sigma_zero :
        schurSigma (scaledCoeffRowsSchur b) i' j' = 0 := by
      show (Id.run do
            let mut sigma :=
              getArrayEntry (scaledCoeffRowsSchur b) i' 0 *
                getArrayEntry (scaledCoeffRowsSchur b) j' 0
            for p in [1:j'] do
              sigma :=
                Matrix.exactDiv
                  (getArrayEntry (scaledCoeffRowsSchur b) p p * sigma +
                    getArrayEntry (scaledCoeffRowsSchur b) i' p *
                    getArrayEntry (scaledCoeffRowsSchur b) j' p)
                  (getArrayEntry (scaledCoeffRowsSchur b) (p - 1) (p - 1))
            return sigma) = 0
      simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
      have h_fold : ∀ (k : Nat), s ≤ k → k ≤ j' - 1 →
          (List.range' 1 k).foldl
            (fun σ p_iter =>
              Matrix.exactDiv
                (getArrayEntry (scaledCoeffRowsSchur b) p_iter p_iter * σ +
                  getArrayEntry (scaledCoeffRowsSchur b) i' p_iter *
                  getArrayEntry (scaledCoeffRowsSchur b) j' p_iter)
                (getArrayEntry (scaledCoeffRowsSchur b) (p_iter - 1) (p_iter - 1)))
            (getArrayEntry (scaledCoeffRowsSchur b) i' 0 *
              getArrayEntry (scaledCoeffRowsSchur b) j' 0) = 0 := by
        intro k
        induction k with
        | zero =>
          intro hsk _hkj'
          have hs_eq : s = 0 := Nat.le_zero.mp hsk
          simp only [List.range'_zero, List.foldl_nil]
          have hj'_ge_s : s ≤ j' := by omega
          have h_j'0 := h_row_s_zero j' hj'n hj'_ge_s
          rw [hs_eq] at h_j'0
          rw [h_j'0]
          simp
        | succ k' ih_k =>
          intro hsk hkj'
          have h_concat :
              List.range' 1 (k' + 1) = List.range' 1 k' ++ [k' + 1] := by
            have := List.range'_concat (s := 1) (n := k') (step := 1)
            simpa [Nat.add_comm 1 k'] using this
          rw [h_concat, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          by_cases hsk' : s ≤ k'
          · -- IH applies: the prefix fold is already zero.
            have hk'_le_j' : k' ≤ j' - 1 := by omega
            have ih_zero := ih_k hsk' hk'_le_j'
            rw [ih_zero]
            have hs_lt_kp1 : s < k' + 1 := Nat.lt_succ_of_le hsk'
            have hkp1_lt_j' : k' + 1 < j' := by omega
            have hkp1_le_j : k' + 1 ≤ j :=
              Nat.le_of_lt (Nat.lt_of_lt_of_le hkp1_lt_j' hj'j)
            have hkp1_lt_n : k' + 1 < n := Nat.lt_trans hkp1_lt_j' hj'n
            have hkp1_le_i' : k' + 1 ≤ i' := by omega
            have hkp1_le_j' : k' + 1 ≤ j' := by omega
            have h_diag :=
              ih (k' + 1) hkp1_lt_j' hkp1_le_j hs_lt_kp1 (k' + 1) (Nat.le_refl _) hkp1_lt_n
            have h_i_pkp1 :=
              ih (k' + 1) hkp1_lt_j' hkp1_le_j hs_lt_kp1 i' hkp1_le_i' hi'n
            have h_j_pkp1 :=
              ih (k' + 1) hkp1_lt_j' hkp1_le_j hs_lt_kp1 j' hkp1_le_j' hj'n
            rw [h_diag, h_i_pkp1, h_j_pkp1]
            simp [Matrix.exactDiv]
          · -- Killing iteration: `s = k' + 1`, so `rows[*][k' + 1] = 0`.
            have hs_eq : s = k' + 1 := by omega
            have hkp1_le_i' : k' + 1 ≤ i' := by omega
            have hkp1_le_j' : k' + 1 ≤ j' := by omega
            have hkp1_lt_n : k' + 1 < n := by omega
            have h_diag : getArrayEntry (scaledCoeffRowsSchur b) (k' + 1) (k' + 1) = 0 := by
              rw [show k' + 1 = s from hs_eq.symm]
              exact h_row_s_zero s hsn (Nat.le_refl _)
            have h_i_pkp1 : getArrayEntry (scaledCoeffRowsSchur b) i' (k' + 1) = 0 := by
              rw [show k' + 1 = s from hs_eq.symm]
              exact h_row_s_zero i' hi'n (by omega)
            have h_j_pkp1 : getArrayEntry (scaledCoeffRowsSchur b) j' (k' + 1) = 0 := by
              rw [show k' + 1 = s from hs_eq.symm]
              exact h_row_s_zero j' hj'n (by omega)
            rw [h_diag, h_i_pkp1, h_j_pkp1]
            simp [Matrix.exactDiv]
      have hsj'_sub_one : s ≤ j' - 1 := by omega
      exact h_fold (j' - 1) hsj'_sub_one (Nat.le_refl _)
    rw [h_diag_zero, h_sigma_zero]
    grind
open _root_.P2MLLL.t00ef6f00 renaming h1 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h1 → _p2mH1


set_option maxRecDepth 8192
/-- The per-row Schur scaled-coefficient kernel and the column-major Bareiss
array path produce identical integer values at every cell. Both arrays
contain the leading Gram determinant `d_{j+1}` on the diagonal and
`d_{j+1} · μ_{i,j}` below the diagonal, with zeros above; the recurrences
differ only in evaluation order. This equivalence is the bridge from the
Schur implementation to the existing invariant infrastructure proven about
`scaledCoeffRows`.

Closure routes the in-bounds `j ≤ i, j ≠ 0` case through Sub-D
(`getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing`) and Sub-C′
(`getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt`); the
out-of-bounds branch (`n ≤ i`) follows from both arrays having size `n`,
so the row entry is `default` on both sides. -/
theorem _root_.Hex.GramSchmidt.Int.__p2m_proof_00ef6f00a82a3b3f020a
    (b : Matrix Int n m) (hquot : StepWitness b) (i j : Nat) :
    getArrayEntry (scaledCoeffRowsSchur b) i j =
      getArrayEntry (scaledCoeffRows b) i j := by
  by_cases hij : i < j
  · rw [_root_.P2MLLL.t00ef6f00.h37 b i j hij,
      _root_.P2MLLL.t00ef6f00.h87 b i j hij]
  · have hji : j ≤ i := Nat.le_of_not_lt hij
    by_cases hj : j = 0
    · subst hj
      rw [_root_.P2MLLL.t00ef6f00.h121 b i,
        _root_.P2MLLL.t00ef6f00.h88 b i]
    · by_cases hin : i < n
      · have hjn : j < n := Nat.lt_of_le_of_lt hji hin
        let iFin : Fin n := ⟨i, hin⟩
        let jFin : Fin n := ⟨j, hjn⟩
        cases h_sing : (Matrix.noPivotLoop j
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep with
        | none =>
          by_cases hij_eq : i = j
          · subst hij_eq
            have h_schur :=
              (_root_.P2MLLL.t00ef6f00.h0
                b hquot i hin h_sing).1
            have h_bareiss :=
              _root_.P2MLLL.t00ef6f00.h18
                b iFin h_sing
            rw [h_schur, h_bareiss]
          · have hji_lt : j < i := Nat.lt_of_le_of_ne hji (Ne.symm hij_eq)
            have h_schur :=
              (_root_.P2MLLL.t00ef6f00.h0
                b hquot j hjn h_sing).2 i hji_lt hin
            have h_bareiss :=
              _root_.P2MLLL.t00ef6f00.h21
                b iFin jFin hji_lt h_sing
            rw [h_schur, h_bareiss]
        | some s =>
          have hsj : s < j := by
            have h := _root_.P2MLLL.t00ef6f00.h2 j
              (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl s h_sing
            show s < j
            simp [Matrix.noPivotInitialState] at h
            exact h
          have h_schur := _root_.P2MLLL.t00ef6f00.h1
            b hquot i j hin hji s hsj h_sing
          rw [h_schur]
          by_cases hij_eq : i = j
          · subst hij_eq
            exact (_root_.P2MLLL.t00ef6f00.h19
              b iFin s hsj h_sing).symm
          · have hji_lt : j < i := Nat.lt_of_le_of_ne hji (Ne.symm hij_eq)
            exact (_root_.P2MLLL.t00ef6f00.h20
              b iFin jFin hji_lt s h_sing).symm
      · have hin' : n ≤ i := Nat.le_of_not_lt hin
        have h_schur_size : (scaledCoeffRowsSchur b).size ≤ i :=
          (_root_.P2MLLL.t00ef6f00.h71 b).symm ▸ hin'
        have h_bareiss_size : (scaledCoeffRows b).size = n := by
          unfold scaledCoeffRows
          rw [_root_.P2MLLL.t00ef6f00.h115]
          exact _root_.P2MLLL.t00ef6f00.h86 n
        have h_bareiss_size_le : (scaledCoeffRows b).size ≤ i :=
          h_bareiss_size.symm ▸ hin'
        have h_schur_default : (scaledCoeffRowsSchur b)[i]! = (default : Array Int) := by
          rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none h_schur_size, Option.getD_none]
        have h_bareiss_default : (scaledCoeffRows b)[i]! = (default : Array Int) := by
          rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none h_bareiss_size_le, Option.getD_none]
        unfold getArrayEntry
        rw [h_schur_default, h_bareiss_default]




























/-! # Coefficient bordered minor and multilinearity entry equation

The `coeffBM` matrix shares its first `k` columns with `borderedMinor G k hk i j`
(those columns do not depend on `j`) and replaces the last column with the
indicator vector picking out row index `a`. The multilinearity entry equation
expands `Matrix.det (borderedMinor G k hk i j)` as a sum over `a` of
`Matrix.det (coeffBM G k hk i a) * G[a][j]`, applying `det_colReplace_sum_finRange`
to the indicator expansion of the last column. -/



end GramSchmidt.Int
open _root_.P2MLLL.t00ef6f00 renaming h0 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing
open _root_.P2MLLL.t00ef6f00 renaming h0 → _p2mH0
open _root_.P2MLLL.t00ef6f00 renaming h1 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h1 → _p2mH1
open _root_.P2MLLL.t00ef6f00 renaming h13 → Hex.GramSchmidt.Int.dot_comm_int
open _root_.P2MLLL.t00ef6f00 renaming h13 → _p2mH13
open _root_.P2MLLL.t00ef6f00 renaming h14 → Hex.GramSchmidt.Int.exactDiv_bareissCorrection_succ_algebra
open _root_.P2MLLL.t00ef6f00 renaming h14 → _p2mH14
open _root_.P2MLLL.t00ef6f00 renaming h15 → Hex.GramSchmidt.Int.foldl_dot_comm_int
open _root_.P2MLLL.t00ef6f00 renaming h15 → _p2mH15
open _root_.P2MLLL.t00ef6f00 renaming h16 → Hex.GramSchmidt.Int.gramMatrix_symm
open _root_.P2MLLL.t00ef6f00 renaming h16 → _p2mH16
open _root_.P2MLLL.t00ef6f00 renaming h17 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_diag_ne_zero
open _root_.P2MLLL.t00ef6f00 renaming h17 → _p2mH17
open _root_.P2MLLL.t00ef6f00 renaming h18 → Hex.GramSchmidt.Int.scaledCoeffRows_diag_eq_noPivotLoop_gramMatrix_of_no_singular
open _root_.P2MLLL.t00ef6f00 renaming h18 → _p2mH18
open _root_.P2MLLL.t00ef6f00 renaming h19 → Hex.GramSchmidt.Int.scaledCoeffRows_diag_eq_zero_of_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h19 → _p2mH19
open _root_.P2MLLL.t00ef6f00 renaming h20 → Hex.GramSchmidt.Int.scaledCoeffRows_eq_zero_of_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h20 → _p2mH20
open _root_.P2MLLL.t00ef6f00 renaming h21 → Hex.GramSchmidt.Int.scaledCoeffRows_lower_eq
open _root_.P2MLLL.t00ef6f00 renaming h21 → _p2mH21
open _root_.P2MLLL.t00ef6f00 renaming h22 → Hex.GramSchmidt.Int.schurSigma_foldl_eq
open _root_.P2MLLL.t00ef6f00 renaming h22 → _p2mH22
open _root_.P2MLLL.t00ef6f00 renaming h23 → Hex.GramSchmidt.Int.schurSigma_noPivotCorrection_succ
open _root_.P2MLLL.t00ef6f00 renaming h23 → _p2mH23


namespace GramSchmidt.Rat



end GramSchmidt.Rat
end Hex
open _root_.P2MLLL.t00ef6f00 renaming h0 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing
open _root_.P2MLLL.t00ef6f00 renaming h0 → _p2mH0
open _root_.P2MLLL.t00ef6f00 renaming h1 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h1 → _p2mH1
open _root_.P2MLLL.t00ef6f00 renaming h13 → Hex.GramSchmidt.Int.dot_comm_int
open _root_.P2MLLL.t00ef6f00 renaming h13 → _p2mH13
open _root_.P2MLLL.t00ef6f00 renaming h14 → Hex.GramSchmidt.Int.exactDiv_bareissCorrection_succ_algebra
open _root_.P2MLLL.t00ef6f00 renaming h14 → _p2mH14
open _root_.P2MLLL.t00ef6f00 renaming h15 → Hex.GramSchmidt.Int.foldl_dot_comm_int
open _root_.P2MLLL.t00ef6f00 renaming h15 → _p2mH15
open _root_.P2MLLL.t00ef6f00 renaming h16 → Hex.GramSchmidt.Int.gramMatrix_symm
open _root_.P2MLLL.t00ef6f00 renaming h16 → _p2mH16
open _root_.P2MLLL.t00ef6f00 renaming h17 → Hex.GramSchmidt.Int.noPivotLoop_initial_gram_diag_ne_zero
open _root_.P2MLLL.t00ef6f00 renaming h17 → _p2mH17
open _root_.P2MLLL.t00ef6f00 renaming h18 → Hex.GramSchmidt.Int.scaledCoeffRows_diag_eq_noPivotLoop_gramMatrix_of_no_singular
open _root_.P2MLLL.t00ef6f00 renaming h18 → _p2mH18
open _root_.P2MLLL.t00ef6f00 renaming h19 → Hex.GramSchmidt.Int.scaledCoeffRows_diag_eq_zero_of_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h19 → _p2mH19
open _root_.P2MLLL.t00ef6f00 renaming h20 → Hex.GramSchmidt.Int.scaledCoeffRows_eq_zero_of_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h20 → _p2mH20
open _root_.P2MLLL.t00ef6f00 renaming h21 → Hex.GramSchmidt.Int.scaledCoeffRows_lower_eq
open _root_.P2MLLL.t00ef6f00 renaming h21 → _p2mH21
open _root_.P2MLLL.t00ef6f00 renaming h22 → Hex.GramSchmidt.Int.schurSigma_foldl_eq
open _root_.P2MLLL.t00ef6f00 renaming h22 → _p2mH22
open _root_.P2MLLL.t00ef6f00 renaming h23 → Hex.GramSchmidt.Int.schurSigma_noPivotCorrection_succ
open _root_.P2MLLL.t00ef6f00 renaming h23 → _p2mH23


/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end
open _root_.P2MLLL.t00ef6f00 renaming h0 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_noPivotLoop_of_nonsing
open _root_.P2MLLL.t00ef6f00 renaming h0 → _p2mH0
open _root_.P2MLLL.t00ef6f00 renaming h1 → Hex.GramSchmidt.Int.getArrayEntry_scaledCoeffRowsSchur_eq_zero_of_singularStep_lt
open _root_.P2MLLL.t00ef6f00 renaming h1 → _p2mH1


set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.Hex.GramSchmidt.Int.__p2m_proof_00ef6f00a82a3b3f020a) := @_root_.Hex.GramSchmidt.Int.__p2m_proof_00ef6f00a82a3b3f020a
