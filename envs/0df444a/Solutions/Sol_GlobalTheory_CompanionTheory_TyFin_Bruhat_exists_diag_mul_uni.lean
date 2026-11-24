-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Bruhat.exists_diag_mul_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:47:29.913522+00:00
-- url     : https://prove2.me/submissions/a6435298-f442-405a-bc91-3f676590bead

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionTwoBlocks
import Theorems.Thm_GroundTheory_Automorphic_borel_diag_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_exists_borel_of_isUpperTriangular
import Theorems.Thm_GroundTheory_Automorphic_mem_borel_iff


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
theorem _root_.solution {y : GL (Fin n) K} (hy : y ∈ borel n K) :
    ∃ t : GL (Fin n) K, (∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) K) i j = 0) ∧
      ∃ u ∈ patSet K (fun i j : Fin n => i < j), y = t⁻¹ * u := by
  have hd := borel_diag_ne_zero hy
  obtain ⟨t, -, htD⟩ := exists_borel_of_isUpperTriangular
    (Matrix.diagonal fun i => ((y : Matrix (Fin n) (Fin n) K) i i)⁻¹)
    (Matrix.blockTriangular_diagonal _) (fun i => by simpa using hd i)
  refine ⟨t, fun i j hij => by rw [htD, Matrix.diagonal_apply_ne _ hij], t * y, ?_, by group⟩
  intro i j
  have hval : ((t * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      ((y : Matrix (Fin n) (Fin n) K) i i)⁻¹ * (y : Matrix (Fin n) (Fin n) K) i j := by
    rw [Units.val_mul, htD, Matrix.diagonal_mul]
  refine ⟨fun e => ?_, fun hne hlt => ?_⟩
  · subst e
    rw [hval, inv_mul_cancel₀ (hd i)]
  · have hji : j < i := lt_of_le_of_ne (not_lt.1 hlt) hne.symm
    rw [hval, (mem_borel_iff y).1 hy i j hji, mul_zero]
end GlobalTheory.CompanionTheory.TyFin.Bruhat
