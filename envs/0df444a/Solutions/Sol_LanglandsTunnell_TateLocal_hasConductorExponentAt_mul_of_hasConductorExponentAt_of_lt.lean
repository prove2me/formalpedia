-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/710c1900-64f5-5408-936c-8b74e34f7582

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open LanglandsTunnell.TateLocal in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (lam nu : (v.adicCompletion K)ˣ →* ℂˣ) (a b : ℕ)
    (hlam : HasConductorExponentAt K v lam a) (hnu : HasConductorExponentAt K v nu b) (hlt : b < a) :
    HasConductorExponentAt K v (lam * nu) a := by
  obtain ⟨hlamTriv, hlamNontriv⟩ := hlam
  obtain ⟨hnuTriv, -⟩ := hnu
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  ·
    rw [MonoidHom.mul_apply, hlamTriv u hu, hnuTriv u (higherUnitsAt_antitone K v hlt.le hu), one_mul]
  · rcases le_or_gt b m with hbm | hmb
    ·
      obtain ⟨u, hu, hne⟩ := hlamNontriv m hm
      exact ⟨u, hu, by rwa [MonoidHom.mul_apply, hnuTriv u (higherUnitsAt_antitone K v hbm hu), mul_one]⟩
    ·
      obtain ⟨u, hu, hne⟩ := hlamNontriv b hlt
      exact ⟨u, higherUnitsAt_antitone K v hmb.le hu, by rwa [MonoidHom.mul_apply, hnuTriv u hu, mul_one]⟩

end S_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt (solution)
