-- Prove2me | solution 1 for HeckeCharacter.raySymbolUnitsHom_fadContentHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0d236738-6cc0-531b-998c-32731eb79199

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_count_coe_fadContentHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_raySymbolUnitsHom_fadContentHom

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem solution
    (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]
    (f : HeightOneSpectrum (𝓞 K) → M) (y : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    raySymbolUnitsHom K f (fadContentHom K y) = ∏ᶠ w : HeightOneSpectrum (𝓞 K), f w ^ placeOrd K y w := by
  show ∏ᶠ w : HeightOneSpectrum (𝓞 K), f w ^ FractionalIdeal.count K w
      ((fadContentHom K y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) = _
  exact finprod_congr fun w => by rw [HeckeCharacter.count_coe_fadContentHom]

end S_HeckeCharacter_raySymbolUnitsHom_fadContentHom
end P2MW
export P2MW.S_HeckeCharacter_raySymbolUnitsHom_fadContentHom (solution)
