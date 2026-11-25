-- Prove2me | solution 1 for GlobalTheory.T.exists_matrix_sqrt_near_one_ultrametric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:19:55.075287+00:00
-- url     : https://prove2.me/submissions/dd988952-f173-44cd-bcab-b4f7a39d87ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametricStatement
import Theorems.Thm_GlobalTheory_matrix_sqrt_near_one_ultrametric


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] (n : ℕ) (σ : K →+* K), Continuous σ → ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) K), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) K, r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K, a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  first | exact @GlobalTheory.matrix_sqrt_near_one_ultrametric | exact GlobalTheory.matrix_sqrt_near_one_ultrametric | (intros; apply GlobalTheory.matrix_sqrt_near_one_ultrametric <;> assumption)
end _root_.GlobalTheory.T
