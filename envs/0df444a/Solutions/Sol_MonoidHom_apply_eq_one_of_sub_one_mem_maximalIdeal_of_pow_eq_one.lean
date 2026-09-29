-- Prove2me | solution 1 for MonoidHom.apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f672007e-851a-59a1-89c9-1895ffcdf50a

import Mathlib
import Theorems.Thm_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one

set_option autoImplicit false

universe u w

open IsLocalRing

theorem solution {G : Type u} {A : Type w} [Group G] [CommRing A] [IsLocalRing A]
    (χ : G →* Aˣ) (g : G) (hprin : (χ g : A) - 1 ∈ IsLocalRing.maximalIdeal A)
    {n : ℕ} (hn : IsUnit (n : A)) (hgn : g ^ n = 1) : χ g = 1 := by
  ext
  refine IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal hprin hn ?_
  have h := congrArg (Units.val) (map_pow χ g n ▸ (congrArg χ hgn).trans (map_one χ))
  simpa using h

end S_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one
end P2MW
export P2MW.S_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one (solution)
