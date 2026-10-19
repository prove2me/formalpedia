-- Prove2me | solution 1 for MIPRE.CL.CLFun.SupportedOn.mapOfPrefix_proj
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:40:34.871307+00:00
-- url     : https://prove2.me/submissions/82eb4a68-928a-4eb4-a1ff-efde2bfa57dc

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Product.lean (solution of MIPRE.CL.CLFun.SupportedOn.mapOfPrefix_proj);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun.SupportedOn
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]
theorem _root_.solution {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (h : T ⊆ U) (j : ℕ) (u : ι → F) : P.mapOfPrefix j (proj U u) = P.mapOfPrefix j u := by
  induction P generalizing T U j u with
  | zero => rfl
  | cons S L next ih =>
    obtain ⟨hS, hnext⟩ := hP
    cases j with
    | zero => rfl
    | succ j =>
      have h₁ : T \ S ⊆ Sᶜ ∩ U := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hi.2, h hi.1⟩
      have h₂ : T \ S ⊆ Sᶜ := fun i hi => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
      simp only [mapOfPrefix_cons_succ, proj_proj_of_subset (hS.trans h), proj_proj]
      rw [ih _ (hnext _) h₁, ih _ (hnext _) h₂]
end MIPRE.CL.CLFun.SupportedOn
