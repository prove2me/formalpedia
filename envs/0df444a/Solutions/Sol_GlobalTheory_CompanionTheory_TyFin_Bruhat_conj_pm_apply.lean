-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Bruhat.conj_pm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:48.295467+00:00
-- url     : https://prove2.me/submissions/cf0fc912-ea18-4116-a00a-dab2dea39159

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionTwoBlocks
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Bruhat_pm_eq_permGL
import Theorems.Thm_GroundTheory_Automorphic_mul_permGL_apply
import Theorems.Thm_GroundTheory_Automorphic_permGL_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES GroundTheory.Automorphic
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Bruhat
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}
namespace GlobalTheory.CompanionTheory.TyFin.Bruhat
theorem _root_.solution (τ : Equiv.Perm (Fin n)) (x : GL (Fin n) K) (i j : Fin n) :
    ((pm K τ * x * (pm K τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      (x : Matrix (Fin n) (Fin n) K) (τ⁻¹ i) (τ⁻¹ j) := by
  rw [pm_eq_permGL, ← map_inv, Units.val_mul, mul_permGL_apply, Units.val_mul, permGL_mul_apply]
end GlobalTheory.CompanionTheory.TyFin.Bruhat
