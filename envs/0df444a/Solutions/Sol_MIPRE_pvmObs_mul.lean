-- Prove2me | solution 1 for MIPRE.pvmObs_mul
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:33:23.27829+00:00
-- url     : https://prove2.me/submissions/8b9c39a8-52c0-4b83-802e-ab44a875de20

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PVM.lean (solution of MIPRE.pvmObs_mul);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Theorems.Thm_MIPRE_IsPVM_orthogonal

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
theorem _root_.solution (h : IsPVM P) (ε δ : Λ → ℂ) :
    pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ) := by
  classical
  have step : ∀ a : Λ, (ε a • P a) * pvmObs P δ = ((ε * δ) a) • P a := by
    intro a
    rw [pvmObs, Finset.mul_sum, Finset.sum_eq_single a]
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.idem]
      rfl
    · intro b _ hb
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.orthogonal (Ne.symm hb), smul_zero]
    · intro hna
      exact absurd (Finset.mem_univ a) hna
  rw [pvmObs, Finset.sum_mul, Finset.sum_congr rfl fun a (_ : a ∈ univ) => step a, pvmObs]
end MIPRE
