-- Prove2me | solution 1 for MIPRE.CL.clDist_famSum
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:28:28.030999+00:00
-- url     : https://prove2.me/submissions/9d8d0d1d-9d0a-4585-b44b-b8afb8f9eb94

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Repeat.lean (solution of MIPRE.CL.clDist_famSum);
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
theorem join_eq_iff (v : Fin k → ι → F) (x : κ → F) : join e v = x ↔ ∀ i, v i = block e i x := by
  constructor
  · rintro rfl i; simp
  · intro h; rw [← join_block e x]; congr 1; funext i; exact h i
end
end MIPRE.CL

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

namespace MIPRE.CL.CLFun
section
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
variable {ℓ : ℕ}
variable (e : Fin k × ι ≃ κ)
/-- **Evaluation is blockwise.** -/
theorem eval_famSum : ∀ (ℓ : ℕ) (P : Fin k → CLFun F ι ℓ) (x : κ → F),
    (famSum e ℓ P).eval x = join e fun i => (P i).eval (block e i x)
  | 0, P, x => by
    funext p
    simp [(P _).eq_zero]
  | ℓ + 1, P, x => by
    have hP : P = fun i => cons (P i).hdS (P i).hdL (P i).tl := funext fun i => (P i).eta
    rw [hP, famSum_succ, eval_cons, eval_famSum ℓ]
    funext p
    simp only [Pi.add_apply, RegLinear.blockSum_apply, join_apply, block_join, blockSet_compl,
      block_proj, eval_cons]
end
end MIPRE.CL.CLFun

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL
set_option linter.unusedSectionVars false
universe u v w
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {κ : Type w}
  [DecidableEq κ] [Fintype κ] {k : ℕ}
theorem _root_.solution [Fintype F] [DecidableEq F] (e : Fin k × ι ≃ κ) {ℓ : ℕ}
    (L R : Fin k → CLFun F ι ℓ) (a b : κ → F) :
    clDist (CLFun.famSum e ℓ L).eval (CLFun.famSum e ℓ R).eval a b =
      ∏ i, clDist (L i).eval (R i).eval (block e i a) (block e i b) := by
  simp only [clDist]
  rw [Finset.prod_div_distrib]
  congr 1
  · rw [← Nat.cast_prod, ← Fintype.card_piFinset]
    congr 1
    refine Finset.card_equiv (blockEquiv e) fun x => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      CLFun.eval_famSum, join_eq_iff, blockEquiv, Equiv.coe_fn_mk]
    exact forall_and.symm
  · rw [← Nat.cast_prod]
    congr 1
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun, Fintype.card_fun,
      ← Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, ← pow_mul, Nat.mul_comm]
end MIPRE.CL
