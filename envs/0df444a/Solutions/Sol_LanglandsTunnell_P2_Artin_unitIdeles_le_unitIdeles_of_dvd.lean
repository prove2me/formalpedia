-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.unitIdeles_le_unitIdeles_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e1adf2e3-5ced-560d-b14d-1bae70ad8ede

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_unitIdeles_le_unitIdeles_of_dvd

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem solution
    (F : Type*) [Field F] [NumberField F] {𝔪 𝔪' : Ideal (𝓞 F)} (h' : 𝔪' ≠ ⊥) (h : 𝔪 ∣ 𝔪') :
    unitIdeles F 𝔪' ≤ unitIdeles F 𝔪 := by
  classical
  intro u hu
  have h0 : 𝔪' ≠ 0 := by rwa [Ne, Submodule.zero_eq_bot]
  refine ⟨hu.1, fun v hv => ?_, hu.2.2⟩
  refine le_trans (hu.2.1 v (dvd_trans hv h)) ?_
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  exact Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr h0) v.associates_irreducible
    (Associates.mk_le_mk_iff_dvd.mpr h)

end S_LanglandsTunnell_P2_Artin_unitIdeles_le_unitIdeles_of_dvd
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_unitIdeles_le_unitIdeles_of_dvd (solution)
