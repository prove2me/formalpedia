-- Prove2me | solution 1 for LanglandsTunnell.Converse.sPartDual_eq_sPart_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e9741b72-b7bb-594c-b522-529e069543b8

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_sPartDual_eq_sPart_inv

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.Converse

theorem solution (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) :
    sPartDual K S Ad μ s = sPart K S Ad μ⁻¹ s := by
  simp only [sPart, sPartDual, MonoidHom.inv_apply]

end S_LanglandsTunnell_Converse_sPartDual_eq_sPart_inv
end P2MW
export P2MW.S_LanglandsTunnell_Converse_sPartDual_eq_sPart_inv (solution)
