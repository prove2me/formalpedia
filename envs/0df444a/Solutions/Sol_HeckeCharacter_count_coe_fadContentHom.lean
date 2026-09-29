-- Prove2me | solution 1 for HeckeCharacter.count_coe_fadContentHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ed0f12aa-f837-5d37-a2a9-4c18586720e8

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_Deep_NTSupply_count_coe_finprod_primeUnit_zpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_count_coe_fadContentHom

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem solution
    (K : Type*) [Field K] [NumberField K]
    (y : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w
      ((fadContentHom K y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) = placeOrd K y w := by
  show FractionalIdeal.count K w
    ((∏ᶠ v : HeightOneSpectrum (𝓞 K), primeUnit K v ^ placeOrd K y v : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) :
      FractionalIdeal ((𝓞 K)⁰) K) = placeOrd K y w
  exact Deep.NTSupply.count_coe_finprod_primeUnit_zpow K (placeOrd K y) (finite_support_placeOrd K y) w

end S_HeckeCharacter_count_coe_fadContentHom
end P2MW
export P2MW.S_HeckeCharacter_count_coe_fadContentHom (solution)
