-- Prove2me | solution 1 for MIPRE.CL.CLFun.mapOfPrefix_downsize
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:39:55.408083+00:00
-- url     : https://prove2.me/submissions/a3d51fa0-c077-4117-b8eb-4c633c88483f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Downsize.lean (solution of MIPRE.CL.CLFun.mapOfPrefix_downsize);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
theorem _root_.solution (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
    (P.downsize b).mapOfPrefix k (downsizeEquiv b u) =
      (downsizeEquiv (ι := ι) b).toLinearMap ∘ₗ (P.mapOfPrefix k u).restrictScalars K ∘ₗ
        (downsizeEquiv (ι := ι) b).symm.toLinearMap := by
  induction P generalizing k u with
  | zero => ext y; simp
  | cons S L₁ next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [downsize_cons, mapOfPrefix_cons_succ, mapOfPrefix_cons_succ, compl_product_univ,
        ← downsizeEquiv_proj, ← downsizeEquiv_proj, LinearEquiv.symm_apply_apply, ih]
end MIPRE.CL.CLFun
