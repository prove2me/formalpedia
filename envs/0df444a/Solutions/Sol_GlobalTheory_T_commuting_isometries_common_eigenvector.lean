-- Prove2me | solution 1 for GlobalTheory.T.commuting_isometries_common_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:23:40.953031+00:00
-- url     : https://prove2.me/submissions/330a2c55-7d21-4936-889a-49a05aa482b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CommutingIsometriesCommonEigenvector
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CommutingIsometriesCommonEigenvectorStatement
import Theorems.Thm_GlobalTheory_exists_common_eigenvector_inner_ne_zero_of_commute_isometry


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (U : Submodule ℂ V), FiniteDimensional ℂ U → ∀ {ι : Type} (A : ι → V →L[ℂ] V) (x₀ : V), x₀ ∈ U → x₀ ≠ 0 → (∀ i, ∀ x ∈ U, A i x ∈ U) → (∀ i x, ‖A i x‖ = ‖x‖) → (∀ i l x, A i (A l x) = A l (A i x)) → ∃ v ∈ U, ⟪v, x₀⟫_ℂ ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i v = c • v := by
  first | exact @GlobalTheory.exists_common_eigenvector_inner_ne_zero_of_commute_isometry | exact GlobalTheory.exists_common_eigenvector_inner_ne_zero_of_commute_isometry | (intros; apply GlobalTheory.exists_common_eigenvector_inner_ne_zero_of_commute_isometry <;> assumption)
end _root_.GlobalTheory.T
