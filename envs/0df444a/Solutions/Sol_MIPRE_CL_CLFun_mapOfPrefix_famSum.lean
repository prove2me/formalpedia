-- Prove2me | solution 1 for MIPRE.CL.CLFun.mapOfPrefix_famSum
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:28:27.115277+00:00
-- url     : https://prove2.me/submissions/bdef80c7-f8f7-444d-bc33-b35e8de337ce

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Repeat.lean (solution of MIPRE.CL.CLFun.mapOfPrefix_famSum);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Repeat

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
variable (e : Fin k × ι ≃ κ)
theorem blockSet_compl (T : Fin k → Finset ι) : (blockSet e T)ᶜ = blockSet e fun i => (T i)ᶜ := by
  ext p; simp
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
section
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
variable {ℓ : ℕ}
theorem eta (P : CLFun F ι (ℓ + 1)) : P = cons P.hdS P.hdL P.tl := by
  cases P; rfl
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
variable {ℓ : ℕ}
variable (e : Fin k × ι ≃ κ)
theorem famSum_succ (S : Fin k → Finset ι) (L : (i : Fin k) → RegLinear F (S i))
    (next : Fin k → (ι → F) → CLFun F ι ℓ) :
    famSum e (ℓ + 1) (fun i => cons (S i) (L i) (next i)) =
      cons (blockSet e S) (RegLinear.blockSum e L) fun v =>
        famSum e ℓ fun i => next i (block e i v) := rfl
end
end MIPRE.CL.CLFun

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
variable {ℓ : ℕ}
variable (e : Fin k × ι ≃ κ)
theorem _root_.solution : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (j : ℕ) (u y : κ → F),
    (famSum e ℓ P).mapOfPrefix j u y = join e fun i => (P i).mapOfPrefix j (block e i u) (block e i y)
  | 0, P, j, u, y => by
    funext p
    simp [(P _).eq_zero]
  | ℓ + 1, P, j, u, y => by
    have hP : P = fun i => cons (P i).hdS (P i).hdL (P i).tl := funext fun i => (P i).eta
    rw [hP, famSum_succ]
    cases j with
    | zero => rfl
    | succ j =>
      rw [mapOfPrefix_cons_succ, solution ℓ]
      congr 1
      funext i
      rw [mapOfPrefix_cons_succ, block_proj, blockSet_compl, block_proj]
end MIPRE.CL.CLFun
