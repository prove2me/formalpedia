-- Prove2me | solution 1 for HeckeCharacter.fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/76cfdedf-b022-5c63-abf2-2e7f3ac4a1ba

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_fadContentHom_mem_coprimeToModulus_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin Deep.NTSupply

theorem solution
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : IsAdjuster K 𝔣 u 1) :
    fadContentHom K (projFin K u) ∈ coprimeToModulus K 𝔣 := by
  rw [HeckeCharacter.fadContentHom_mem_coprimeToModulus_iff]
  intro w hw
  rw [placeOrd_eq_zero_iff]
  have h := (hu.cong w hw).1
  rw [map_one, inv_one, mul_one] at h
  exact h

end S_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one
end P2MW
export P2MW.S_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one (solution)
