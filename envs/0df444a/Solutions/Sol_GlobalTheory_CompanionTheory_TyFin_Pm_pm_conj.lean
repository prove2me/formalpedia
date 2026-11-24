-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Pm.pm_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:56.10881+00:00
-- url     : https://prove2.me/submissions/d0927c6e-3b9c-40a9-9376-7e67c0d6a766

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_pm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_glEquiv_apply

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Pm
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.TyFin.Pm
theorem _root_.solution (σ : Equiv.Perm ι) (g : GL ι K) :
    pm K σ * g * (pm K σ)⁻¹ = glEquiv K σ g := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, pm_apply, glEquiv_apply]
  rw [Finset.sum_eq_single (σ.symm i), Finset.sum_eq_single (σ j)]
  · simp
  · intro x _ hx
    simp [hx]
  · simp
  · intro x _ hx
    have : i ≠ σ x := fun h => hx (by rw [h]; simp)
    simp [this]
  · simp
end GlobalTheory.CompanionTheory.TyFin.Pm
