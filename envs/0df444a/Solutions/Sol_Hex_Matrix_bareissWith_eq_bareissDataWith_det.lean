-- Prove2me | solution 1 for Hex.Matrix.bareissWith_eq_bareissDataWith_det
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T04:37:50.843097+00:00
-- url     : https://prove2.me/submissions/5156b811-7933-44de-aa13-7f053ebc0fe4

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/



import Definitions.Def_LARLLL_BareissProgram
import Init
import Init.Data.List.Sort.Basic
import Init.Grind.Ring.Field
import Std
import Std.Data.ExtTreeMap.Lemmas
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























































































section GenericBareiss

variable [Zero R] [One R] [Neg R] [Sub R] [Mul R] [DecidableEq R]
variable {quot : R → R → R}































































set_option maxRecDepth 8192
/-- The public row-pivoted determinant agrees with the determinant encoded by
`bareissDataWith`. This separates executable array evaluation from the packaged
elimination data used by correctness proofs. -/
-- @[grind]-excluded: one-shot executable-vs-packaged determinant bridge.
theorem _root_.Hex.Matrix.__p2m_proof_02a438289a13ad7d33c8 (M : Matrix R n n) :
    bareissWith quot M = (bareissDataWith quot M).det := by
  cases n with
  | zero =>
      simp [bareissWith, bareissDataWith, bareissArrayDet, BareissData.det,
        arrayLastDiag?, BareissData.lastDiag?, arraySign, BareissData.sign]
      rfl
  | succ k =>
      simp [bareissWith, bareissDataWith, bareissArrayDet, BareissData.det,
        arrayLastDiag?, BareissData.lastDiag?, rowsToMatrix,
        arraySign, BareissData.sign]
      cases (bareissArrayStateWith quot M).singularStep with
      | some s => rfl
      | none =>
          exact congrArg
            (fun x =>
              (if (bareissArrayStateWith quot M).rowSwaps % 2 = 0 then (1 : R) else -1) * x)
            (Matrix.getElem_ofFn
              (fun i j => getEntry (bareissArrayStateWith quot M).matrix i.val j.val)
              ⟨k, Nat.lt_succ_self k⟩ ⟨k, Nat.lt_succ_self k⟩).symm



end GenericBareiss

















/-! Integer proof-interface compatibility.  These theorems state their
conclusions through the traditional entry points while delegating every proof
to the generic `With` theorem. -/























































end Matrix
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end


set_option maxRecDepth 65536
theorem solution.{u} : (type_of% @_root_.Hex.Matrix.__p2m_proof_02a438289a13ad7d33c8.{u}) := @_root_.Hex.Matrix.__p2m_proof_02a438289a13ad7d33c8.{u}
