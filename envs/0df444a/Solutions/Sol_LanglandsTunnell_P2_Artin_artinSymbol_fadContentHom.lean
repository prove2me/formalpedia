-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.artinSymbol_fadContentHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/943a9b45-9a85-5060-80a9-4ffffb76818d

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_raySymbolUnitsHom_fadContentHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_artinSymbol_fadContentHom

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem solution
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    [IsMulCommutative (M ≃ₐ[K] M)] (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : fadContentHom K (projFin K u) ∈ coprimeToModulus K 𝔣) :
    artinSymbol K M 𝔣 ⟨fadContentHom K (projFin K u), hu⟩ =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinFrob K M v ^ placeOrd K (projFin K u) v := by
  show raySymbolUnitsHom K (artinFrob K M) (fadContentHom K (projFin K u)) = _
  exact HeckeCharacter.raySymbolUnitsHom_fadContentHom K (artinFrob K M) (projFin K u)

end S_LanglandsTunnell_P2_Artin_artinSymbol_fadContentHom
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_artinSymbol_fadContentHom (solution)
