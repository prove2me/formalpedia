-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5a35b5aa-140b-5a2e-b37b-e5c84749c023

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_DedekindDomain_IntegralClosure
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_zero

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum LanglandsTunnell.TateLocal

theorem solution
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (χ : (v.adicCompletion E)ˣ →* ℂˣ) (hχ : HasConductorExponentAt E v χ 0) :
    HasConductorExponentAt M w.1 (χ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) 0 := by
  rw [hasConductorExponentAt_zero_iff] at hχ ⊢
  intro u hu
  show χ (Units.map (Algebra.norm (v.adicCompletion E)) u) = 1
  apply hχ
  show Valued.v (Algebra.norm (v.adicCompletion E) (u : w.1.adicCompletion M)) = 1
  rw [M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg E M v w (u : w.1.adicCompletion M), hu, one_pow]

end S_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_zero
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_zero (solution)
