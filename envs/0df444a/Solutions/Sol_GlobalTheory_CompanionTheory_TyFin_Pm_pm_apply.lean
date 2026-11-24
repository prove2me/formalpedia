-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Pm.pm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:02.768083+00:00
-- url     : https://prove2.me/submissions/654e74d2-5b5e-451a-af9f-a1a92e4321b5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties

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
omit [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin.Pm
theorem _root_.solution (σ : Equiv.Perm ι) (i j : ι) :
    (pm K σ : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
  show (Matrix.permMatrixHom (n := ι) (R := K) σ) i j = _
  rw [Matrix.permMatrixHom_apply]
  show (σ⁻¹ : Equiv.Perm ι).toPEquiv.toMatrix i j = _
  rw [PEquiv.toMatrix_apply]
  by_cases h : i = σ j
  · subst h
    simp
  · have h' : j ≠ σ.symm i := fun e => h (by rw [e, Equiv.apply_symm_apply])
    simp [h, Ne.symm h']
end GlobalTheory.CompanionTheory.TyFin.Pm
