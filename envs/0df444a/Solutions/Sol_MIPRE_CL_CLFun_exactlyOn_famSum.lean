-- Prove2me | solution 1 for MIPRE.CL.CLFun.exactlyOn_famSum
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:28:24.69738+00:00
-- url     : https://prove2.me/submissions/26187ff9-19a9-438f-b653-22d9e0def44d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Repeat.lean (solution of MIPRE.CL.CLFun.exactlyOn_famSum);
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
theorem e_mem_blockSet (T : Fin k → Finset ι) (i : Fin k) (j : ι) :
    e (i, j) ∈ blockSet e T ↔ j ∈ T i := by simp
end
end MIPRE.CL

namespace MIPRE.CL
section
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
variable (e : Fin k × ι ≃ κ)
theorem blockSet_sdiff (T T' : Fin k → Finset ι) :
    blockSet e T \ blockSet e T' = blockSet e fun i => T i \ T' i := by
  ext p; simp
end
end MIPRE.CL

namespace MIPRE.CL
section
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
variable (e : Fin k × ι ≃ κ)
theorem blockSet_subset {T T' : Fin k → Finset ι} (h : ∀ i, T i ⊆ T' i) :
    blockSet e T ⊆ blockSet e T' := fun p hp => by
  rw [mem_blockSet] at hp ⊢; exact h _ hp
end
end MIPRE.CL

namespace MIPRE.CL
section
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
variable (e : Fin k × ι ≃ κ)
theorem blockSet_eq_empty_iff (T : Fin k → Finset ι) : blockSet e T = ∅ ↔ ∀ i, T i = ∅ := by
  constructor
  · intro h i
    ext j
    simp only [Finset.notMem_empty, iff_false]
    intro hj
    have : e (i, j) ∈ blockSet e T := (e_mem_blockSet e T i j).2 hj
    rw [h] at this
    exact Finset.notMem_empty _ this
  · intro h
    ext p
    simp [h]
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
theorem _root_.solution : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (T : Fin k → Finset ι),
    (∀ i, (P i).ExactlyOn (T i)) → (famSum e ℓ P).ExactlyOn (blockSet e T)
  | 0, P, T, h => by
    show blockSet e T = ∅
    rw [blockSet_eq_empty_iff]
    intro i
    have := h i
    rw [(P i).eq_zero] at this
    exact this
  | ℓ + 1, P, T, h => by
    have hP : P = fun i => cons (P i).hdS (P i).hdL (P i).tl := funext fun i => (P i).eta
    rw [hP] at h ⊢
    rw [famSum_succ]
    refine ⟨blockSet_subset e fun i => (h i).1, fun v => ?_⟩
    rw [blockSet_sdiff]
    exact solution ℓ _ _ fun i => (h i).2 _
end MIPRE.CL.CLFun
