-- Prove2me | solution 1 for GlobalTheory.T.exists_continuous_congruence_near_symmetric_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:12.705488+00:00
-- url     : https://prove2.me/submissions/3b00d776-f851-43a1-9b78-52a3d1bf490e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousCongruenceNearSymmetricMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousCongruenceNearSymmetricMatrixStatement
import Theorems.Thm_GlobalTheory_symm_congr_local_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (H₀ : Matrix (Fin r) (Fin r) F), H₀.IsSymm → H₀.det ≠ 0 → ∃ (Ω : Set (Matrix (Fin r) (Fin r) F)) (k : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F), IsOpen Ω ∧ H₀ ∈ Ω ∧ ContinuousOn k Ω ∧ k H₀ = 1 ∧ ∀ H ∈ Ω, H.IsSymm → (k H)ᵀ * H₀ * k H = H := by
  first | exact @GlobalTheory.symm_congr_local_continuous | exact GlobalTheory.symm_congr_local_continuous | (intros; apply GlobalTheory.symm_congr_local_continuous <;> assumption)
end _root_.GlobalTheory.T
