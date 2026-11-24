-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:08:19.988375+00:00
-- url     : https://prove2.me/submissions/bb2d2655-be6f-4f9f-9678-44b217afe65e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExpBlockTriangular
import Theorems.Thm_GlobalTheory_CompanionTheory_Unitary_ExpUpper_blockTriangular_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Unitary GlobalTheory.CompanionTheory.Unitary.ExpUpper
namespace GlobalTheory.CompanionTheory.Unitary.ExpUpper
theorem _root_.solution {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (h : (Uᴴ * Y * U).BlockTriangular id) :
    (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hunit : IsUnit U := ⟨⟨U, Uᴴ, hUU', hUU⟩, rfl⟩
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hUU
  rw [← hinv, ← Matrix.exp_conj' U Y hunit]
  exact GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_exp _ (hinv ▸ h)
end GlobalTheory.CompanionTheory.Unitary.ExpUpper
