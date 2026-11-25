-- Prove2me | solution 1 for GlobalTheory.AdicCoord.eq_zero_of_forall_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:46.795314+00:00
-- url     : https://prove2.me/submissions/20ddcdb7-96d4-4ff3-88b4-7f79bb9d7efa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAdicCoordinatesOfBasisModP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdicCoord
namespace GlobalTheory.AdicCoord
theorem _root_.solution {R : Type} [CommRing R] (x : R)
    [IsHausdorff (Ideal.span {x}) R] (y : R) (h : ∀ N : ℕ, x ^ N ∣ y) : y = 0 := by
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {x}) R) y fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact h N
end GlobalTheory.AdicCoord
