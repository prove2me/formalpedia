-- Prove2me | solution 1 for LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7fae40b5-46e7-535d-b7a4-7070c3793aa6

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal LanglandsTunnell.TateLocal

open NumberField.TateGlobal LanglandsTunnell.TateLocal in

theorem solution
    (K : Type) [Field K]
    [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (h : IsUnramifiedCharAt μ v) : HasConductorExponentAt K v (localChar μ v) 0 := by
  rw [hasConductorExponentAt_zero_iff]
  intro u hu
  refine h u ?_ ?_
  · change Valued.v (u : v.adicCompletion K) ≤ 1
    exact hu.le
  · change Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

end S_LanglandsTunnell_Converse_hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt
end P2MW
export P2MW.S_LanglandsTunnell_Converse_hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt (solution)
