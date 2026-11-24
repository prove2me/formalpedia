-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:33.189445+00:00
-- url     : https://prove2.me/submissions/7d906b1a-4fa1-46ac-9db3-9f577cd07a70

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspVan
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.TyFin.CuspVan
theorem _root_.solution {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K) (i j : ι) :
    (extHom b c v : Matrix ι ι K) i j =
      if h : b i = c ∧ b j = c then (v : Matrix {i // b i = c} {i // b i = c} K) ⟨i, h.1⟩ ⟨j, h.2⟩ else if i = j then 1 else 0 := by
  have h0 : (extHom b c v : Matrix ι ι K) =
      (Matrix.fromBlocks (v : Matrix {i // b i = c} {i // b i = c} K) 0 0 1).submatrix
        (Equiv.sumCompl (fun i => b i = c)).symm (Equiv.sumCompl (fun i => b i = c)).symm := rfl
  rw [h0, Matrix.submatrix_apply]
  by_cases hi : b i = c <;> by_cases hj : b j = c
  · simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos]
  · have : i ≠ j := fun h => hj (h ▸ hi)
    simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg, this]
  · have : i ≠ j := fun h => hi (h ▸ hj)
    simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg, this]
  · simp [hi, hj, Equiv.sumCompl_symm_apply_of_neg, Matrix.one_apply, Subtype.ext_iff]
end GlobalTheory.CompanionTheory.TyFin.CuspVan
