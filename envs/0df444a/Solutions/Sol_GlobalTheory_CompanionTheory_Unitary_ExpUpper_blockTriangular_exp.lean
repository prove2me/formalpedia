-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:35.938503+00:00
-- url     : https://prove2.me/submissions/d1bdfb5a-7802-4983-9c89-241742130882

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExpBlockTriangular

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
open scoped Matrix.Norms.L2Operator
namespace GlobalTheory.CompanionTheory.Unitary.ExpUpper
theorem _root_.solution {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.BlockTriangular id) : (NormedSpace.exp T).BlockTriangular id := by
  have hmem : ∀ k : ℕ, ((k.factorial : ℂ)⁻¹ • T ^ k) ∈ Matrix.blockTriangularSubalgebra ℂ ℂ id := fun k =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ ((Matrix.mem_blockTriangularSubalgebra).mpr hT) k) _

  refine (isClosed_setOfPred_blockTriangular (b := id)).mem_of_tendsto
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (x := T)) (Filter.Eventually.of_forall fun s => ?_)
  exact (Matrix.mem_blockTriangularSubalgebra).mp (Subalgebra.sum_mem _ fun k _ => hmem k)
end GlobalTheory.CompanionTheory.Unitary.ExpUpper
