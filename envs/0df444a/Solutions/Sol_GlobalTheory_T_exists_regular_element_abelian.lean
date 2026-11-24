-- Prove2me | solution 1 for GlobalTheory.T.exists_regular_element_abelian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:03.887415+00:00
-- url     : https://prove2.me/submissions/5f96ec2c-a803-405a-9ced-ee64e373b306

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsRegularElementAbelian
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsRegularElementAbelianStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_IwaGen_exists_regular_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {n : ℕ} (𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ), ∃ H ∈ 𝔞, ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → ∀ A ∈ 𝔞, (Uᴴ * A * U) i i = (Uᴴ * A * U) j j := by
  first | exact @GlobalTheory.CompanionTheory.IwaGen.exists_regular_point | exact GlobalTheory.CompanionTheory.IwaGen.exists_regular_point | (intros; apply GlobalTheory.CompanionTheory.IwaGen.exists_regular_point <;> assumption)
end _root_.GlobalTheory.T
