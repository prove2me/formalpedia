-- Prove2me | solution 1 for MIPRE.CL.CLFun.eval_truncate_downsize
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:39:54.119493+00:00
-- url     : https://prove2.me/submissions/33d39efa-07a6-4ee9-aef0-650f67ff6806

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Downsize.lean (solution of MIPRE.CL.CLFun.eval_truncate_downsize);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Downsize

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
theorem sdiff_product_univ (S T : Finset ι) :
    (T ×ˢ (Finset.univ : Finset κ)) \ (S ×ˢ Finset.univ) = (T \ S) ×ˢ Finset.univ := by
  ext ⟨i, j⟩; simp
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
theorem lift_downsize (b : Module.Basis κ K F) (T : Finset ι) (P : CLFun F ι ℓ) :
    (P.lift T).downsize b = (P.downsize b).lift (T ×ˢ Finset.univ) := by
  induction P generalizing T with
  | zero => simp [lift]
  | cons S L₁ next ih =>
    simp only [lift, downsize_cons]
    congr 1
    funext v
    rw [ih, sdiff_product_univ]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
theorem truncate_downsize (b : Module.Basis κ K F) (k : ℕ) (P : CLFun F ι ℓ) :
    (P.downsize b).truncate k = (P.truncate k).downsize b := by
  induction k generalizing ℓ P with
  | zero => simp
  | succ k ih =>
    cases P with
    | zero =>
      rw [downsize_zero, truncate_succ_zero, truncate_succ_zero, lift_downsize, ← ih,
        downsize_zero, Finset.empty_product]
    | cons S L₁ next =>
      rw [downsize_cons, truncate_succ_cons, truncate_succ_cons, downsize_cons]
      congr 1
      funext v
      exact ih _
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
theorem compl_product_univ (S : Finset ι) :
    (S ×ˢ (Finset.univ : Finset κ))ᶜ = Sᶜ ×ˢ Finset.univ := by
  ext ⟨i, j⟩; simp
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
/-- `L^↓ = ↓ ∘ L ∘ ↓⁻¹`. -/
theorem eval_downsize (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.downsize b).eval (downsizeEquiv b x) = downsizeEquiv b (P.eval x) := by
  induction P generalizing x with
  | zero => simp
  | cons S L₁ next ih =>
    rw [downsize_cons, eval_cons, eval_cons, RegLinear.downsize_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, compl_product_univ,
      ← downsizeEquiv_proj, ih, map_add]
end
end MIPRE.CL.CLFun

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
theorem _root_.solution (b : Module.Basis κ K F) (k : ℕ) (P : CLFun F ι ℓ) (x : ι → F) :
    ((P.downsize b).truncate k).eval (downsizeEquiv b x) =
      downsizeEquiv b ((P.truncate k).eval x) := by
  rw [truncate_downsize, eval_downsize]
end MIPRE.CL.CLFun
