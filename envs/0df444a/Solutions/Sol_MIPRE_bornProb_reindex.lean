-- Prove2me | solution 1 for MIPRE.bornProb_reindex
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:34:02.070789+00:00
-- url     : https://prove2.me/submissions/72b3fea3-db1f-43d0-9624-12287ac2f3ed

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/RegisterReindex.lean (solution of MIPRE.bornProb_reindex);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB dA' dB' : Type*}
/-- The Kronecker product of two reindexed matrices is the reindexing of the Kronecker product
along the product equivalence. -/
theorem reindex_kronecker_reindex (eA : dA ≃ dA') (eB : dB ≃ dB') (M : Matrix dA dA ℂ)
    (N : Matrix dB dB ℂ) :
    Matrix.reindex eA eA M ⊗ₖ Matrix.reindex eB eB N
      = Matrix.reindex (Equiv.prodCongr eA eB) (Equiv.prodCongr eA eB) (M ⊗ₖ N) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, kroneckerMap_apply]
end
end MIPRE

namespace MIPRE
section
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB dA' dB' : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dA'] [Fintype dB']
/-- **The Born rule is invariant under reindexing.** -/
theorem quadForm_reindex (eA : dA ≃ dA') (eB : dB ≃ dB') (ψ : dA × dB → ℂ)
    (M : Matrix dA dA ℂ) (N : Matrix dB dB ℂ) :
    star (reindexVec eA eB ψ) ⬝ᵥ
        ((Matrix.reindex eA eA M ⊗ₖ Matrix.reindex eB eB N) *ᵥ reindexVec eA eB ψ)
      = star ψ ⬝ᵥ ((M ⊗ₖ N) *ᵥ ψ) := by
  set E := Equiv.prodCongr eA eB with hE
  rw [reindex_kronecker_reindex, reindexVec, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  have hcomp : (ψ ∘ E.symm) ∘ E.symm.symm = ψ := by
    rw [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  rw [hcomp]
  show ∑ p, star ψ (E.symm p) * ((M ⊗ₖ N) *ᵥ ψ) (E.symm p)
    = ∑ p, star ψ p * ((M ⊗ₖ N) *ᵥ ψ) p
  exact Equiv.sum_comp E.symm fun p => star ψ p * ((M ⊗ₖ N) *ᵥ ψ) p
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB dA' dB' : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dA'] [Fintype dB']
theorem _root_.solution (eA : dA ≃ dA') (eB : dB ≃ dB') (ψ : dA × dB → ℂ)
    (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
    bornProb (reindexVec eA eB ψ) (Matrix.reindex eA eA EA) (Matrix.reindex eB eB EB)
      = bornProb ψ EA EB := by
  rw [bornProb, bornProb, quadForm_reindex]
end MIPRE
