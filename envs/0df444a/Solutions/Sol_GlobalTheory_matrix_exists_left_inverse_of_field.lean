-- Prove2me | solution 1 for GlobalTheory.matrix_exists_left_inverse_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:51.540491+00:00
-- url     : https://prove2.me/submissions/42714211-da63-4d7d-9eed-d41e8ecd7cd0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLeftInverseOfFibrewiseInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {m n : ℕ}
    (Q : Matrix (Fin m) (Fin n) K) (h : Function.Injective Q.mulVec) :
    ∃ Q' : Matrix (Fin n) (Fin m) K, Q' * Q = 1 := by
  have hk : LinearMap.ker (Matrix.toLin' Q) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    apply h
    simpa [Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
end GlobalTheory
