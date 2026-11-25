-- Prove2me | solution 1 for GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:23:35.940814+00:00
-- url     : https://prove2.me/submissions/5da11dea-c4d6-40bb-b4d6-d3251c056e2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactPreimageQuadraticMapNoNullVectors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactPreimageQuadraticMapNoNullVectorsStatement
import Theorems.Thm_GlobalTheory_quadratic_preimage_compact_on_subspace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (m : ℕ) (S : Submodule K (Matrix (Fin m) (Fin m) K)) (q : Matrix (Fin m) (Fin m) K → Matrix (Fin m) (Fin m) K), Continuous q → (∀ (c : K) w, q (c • w) = (c * star c) • q w) → (∀ w ∈ S, q w = 0 → w = 0) → ∀ Q : Set (Matrix (Fin m) (Fin m) K), IsCompact Q → ∃ B : Set (Matrix (Fin m) (Fin m) K), IsCompact B ∧ ∀ w ∈ S, q w ∈ Q → w ∈ B := by
  first | exact @GlobalTheory.quadratic_preimage_compact_on_subspace | exact GlobalTheory.quadratic_preimage_compact_on_subspace | (intros; apply GlobalTheory.quadratic_preimage_compact_on_subspace <;> assumption)
end _root_.GlobalTheory.T
