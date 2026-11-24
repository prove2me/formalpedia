-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspIff.pm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:44:17.875879+00:00
-- url     : https://prove2.me/submissions/b6635d0e-ae7b-4e4f-ad06-42ceb41a220f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanish

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
open Polynomial CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspIff
namespace GlobalTheory.CompanionTheory.TyFin.CuspIff
theorem _root_.solution {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (g : GL ι K) : pm K σ * g * (pm K σ)⁻¹ = glEquiv K σ g := by
  have hp : ∀ i j, (pm K σ : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
    intro i j
    show (Equiv.toPEquiv σ⁻¹).toMatrix i j = _
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    exact if_congr Equiv.Perm.inv_eq_iff_eq rfl rfl
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  have hg : ∀ x : GL ι K, ((glEquiv K σ x : GL ι K) : Matrix ι ι K) = (x : Matrix ι ι K).submatrix σ.symm σ.symm :=
    fun _ => rfl
  simp only [Units.val_mul, Matrix.mul_apply, hp, hg, Matrix.submatrix_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm i) (fun x _ hx => if_neg (fun h => hx (by simp [h]))) (by simp)]
  simp
end GlobalTheory.CompanionTheory.TyFin.CuspIff
