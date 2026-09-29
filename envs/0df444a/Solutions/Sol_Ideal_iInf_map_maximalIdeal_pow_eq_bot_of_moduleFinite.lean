-- Prove2me | solution 1 for Ideal.iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/750ffbaf-c15d-5b79-93ef-7c1f8ba2fc3b

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    (S : Type*) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (C : Type*) [CommRing C] [Algebra S C] [Module.Finite S C] [Nontrivial C] :
    ⨅ n : ℕ, (maximalIdeal S ^ n).map (algebraMap S C) = ⊥ := by
  have h := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := maximalIdeal S) (M := C)
    (maximalIdeal.isMaximal S).ne_top
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ (⨅ i : ℕ, (maximalIdeal S ^ i • ⊤ : Submodule S C)) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [Ideal.smul_top_eq_map]
    exact (Submodule.mem_iInf _).mp hx i
  rw [h] at hx'
  exact hx'

end S_Ideal_iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite
end P2MW
export P2MW.S_Ideal_iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite (solution)
