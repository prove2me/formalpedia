-- Prove2me | solution 1 for MvFormalGroup.CartierModule.tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/173048af-21ec-5ff0-bf29-a6572d50046a

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective
        (MvFormalGroup.CartierModule.tangent :
          MvFormalGroup.CartierModule p Φ → Fin d → R) ∧
      ∀ f : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.tangent f = 0 ↔
          ∃ g : MvFormalGroup.CartierModule p Φ,
            MvFormalGroup.CartierModule.verschiebung g = f :=
  ⟨MvFormalGroup.CartierModule.tangent_surjective p Φ,
    MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebung_eq p Φ⟩

end S_MvFormalGroup_CartierModule_tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq (solution)
