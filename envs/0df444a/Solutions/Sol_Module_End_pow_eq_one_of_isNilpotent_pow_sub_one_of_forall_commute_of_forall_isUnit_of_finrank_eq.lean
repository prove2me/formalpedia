-- Prove2me | solution 1 for Module.End.pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1641bd34-8657-5613-aa9d-8e98d4ad5b78

import Mathlib
import Theorems.Thm_Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq

set_option autoImplicit false

theorem solution
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {D : Type*} [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x)
    (ι : D →ₐ[F] Module.End F V) (hdim : Module.finrank F D = Module.finrank F V)
    {g : Module.End F V} (hcomm : ∀ d : D, Commute (ι d) g) {e : ℕ}
    (he : IsNilpotent (g ^ e - 1)) : g ^ e = 1 :=
  sub_eq_zero.mp <|
    Module.End.eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq hD ι hdim
      (N := g ^ e - 1) (fun d => ((hcomm d).pow_right e).sub_right (Commute.one_right _)) he

end S_Module_End_pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq
end P2MW
export P2MW.S_Module_End_pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq (solution)
