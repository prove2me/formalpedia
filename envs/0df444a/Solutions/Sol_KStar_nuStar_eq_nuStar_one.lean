-- Prove2me | solution 1 for KStar.nuStar_eq_nuStar_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:38.914019+00:00
-- url     : https://prove2.me/submissions/40e24c5d-8ff0-45a7-80f0-0bda6c108590

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots
import Theorems.Thm_KStar_emultiplicity_pow_sub_one_of_not_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar
variable {R : Type*} [CommRing R] [IsDomain R]
namespace KStar
theorem _root_.solution {p : R} (hp : Prime p) {U : Set R} (hU : ∀ u ∈ U, p ∣ u - 1)
    {tr : ℕ} (htr : ¬ p ∣ (tr : R)) : nuStar p U tr = nuStar p U 1 := by
  unfold nuStar
  congr 1
  refine Set.image_congr fun u hu => ?_
  rw [pow_one]
  exact emultiplicity_pow_sub_one_of_not_dvd hp (hU u hu) htr
end KStar
