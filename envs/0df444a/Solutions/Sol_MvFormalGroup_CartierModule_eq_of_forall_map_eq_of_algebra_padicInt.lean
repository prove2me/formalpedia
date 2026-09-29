-- Prove2me | solution 1 for MvFormalGroup.CartierModule.eq_of_forall_map_eq_of_algebra_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ce9f5452-7b20-5938-8116-728699b7a22f

import Theorems.Thm_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq
import Theorems.Thm_MvFormalGroup_CartierModule_subst_curve_eq_of_forall_map_eq_of_algebra_padicInt
import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_eq_of_forall_map_eq_of_algebra_padicInt
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R]
    [Algebra (PadicInt p) R]
    {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (φ ψ : Φ.Hom Φ')
    (h : ∀ f : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.map φ f = MvFormalGroup.CartierModule.map ψ f) :
    φ = ψ := by
  exact MvFormalGroup.Hom.eq_of_forall_subst_curve_eq Φ Φ' φ ψ
    (fun γ hγ k => MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt p Φ Φ' φ ψ h γ hγ k)

end S_MvFormalGroup_CartierModule_eq_of_forall_map_eq_of_algebra_padicInt
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_eq_of_forall_map_eq_of_algebra_padicInt (solution)
