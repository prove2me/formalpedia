-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:08:14.421254+00:00
-- url     : https://prove2.me/submissions/a2e0351b-bedb-4c1f-9e16-cdf4be761c5f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GLTransitiveNonzeroVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_RowTrans_exists_linearEquiv_apply_eq_of_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.RowTrans
namespace GlobalTheory.CompanionTheory.TyFin.RowTrans
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by
  intro K _ _ _ j r r' hr hr'
  obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.TyFin.RowTrans.exists_linearEquiv_apply_eq_of_ne_zero (K := K) hr hr'
  have h1 : (e.symm : (Fin j → K) →ₗ[K] Fin j → K) ∘ₗ (e : (Fin j → K) →ₗ[K] Fin j → K) =
      LinearMap.id := LinearMap.ext fun v => by simp
  have h2 : (e : (Fin j → K) →ₗ[K] Fin j → K) ∘ₗ (e.symm : (Fin j → K) →ₗ[K] Fin j → K) =
      LinearMap.id := LinearMap.ext fun v => by simp
  refine ⟨⟨(LinearMap.toMatrix' (e : (Fin j → K) →ₗ[K] Fin j → K)).transpose,
    (LinearMap.toMatrix' (e.symm : (Fin j → K) →ₗ[K] Fin j → K)).transpose, ?_, ?_⟩, ?_⟩
  · rw [← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  · change Matrix.vecMul r (LinearMap.toMatrix' (e : (Fin j → K) →ₗ[K] Fin j → K)).transpose = r'
    rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
    exact he
end GlobalTheory.CompanionTheory.TyFin.RowTrans
