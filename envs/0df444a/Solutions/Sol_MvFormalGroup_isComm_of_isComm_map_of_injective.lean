-- Prove2me | solution 1 for MvFormalGroup.isComm_of_isComm_map_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/73c49708-e7e7-5575-ba2a-e5226c08f2f9

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

namespace P2MW.S_MvFormalGroup_isComm_of_isComm_map_of_injective

set_option autoImplicit false

universe u

open MvPowerSeries

theorem solution
    {g : ℕ} {R : Type u} {S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (F : MvFormalGroup g R)
    (hc : (MvFormalGroup.map φ F).IsComm) : F.IsComm := by
  constructor
  intro i
  have hsw : HasSubst (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  have h : subst (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) S))
        fun j => X (Sum.inl j)) (MvPowerSeries.map φ (F.toPowerSeries i))
      = MvPowerSeries.map φ (F.toPowerSeries i) := hc.comm i
  have hfam : (fun s => ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j)) s).map φ)
      = Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) S))
          fun j => X (Sum.inl j) := by
    funext s; rcases s with j | j <;> simp [map_X]
  rw [← hfam, ← map_subst hsw] at h
  ext n
  apply hφ
  rw [← coeff_map, ← coeff_map, h]

end S_MvFormalGroup_isComm_of_isComm_map_of_injective
end P2MW
export P2MW.S_MvFormalGroup_isComm_of_isComm_map_of_injective (solution)
