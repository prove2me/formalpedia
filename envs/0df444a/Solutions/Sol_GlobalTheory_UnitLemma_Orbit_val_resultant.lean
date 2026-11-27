-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.val_resultant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:47.670403+00:00
-- url     : https://prove2.me/submissions/bb1fdfd3-81b1-4a7e-bf1e-a8f3548e9635

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_val_unit
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_charpoly_dvd_map_of_aeval_eq_zero
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_Orbit_exists_monic_map_eq_charpoly__518c0881fa8f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (B C : InvAlg K) (hB : B.P.Separable) (hC : C.P.Separable) (iB : IsIntegral K.O B.g)
    (iC : IsIntegral K.O C.g) (f : K.O[X]) (h0 : aeval B.g f = 0) (h1 : aeval C.g f = 1) :
    val K.O (resultant B.P C.P) = 0 := by
  obtain ⟨p, hp, ep⟩ := exists_monic_map_eq_charpoly₂ B hB iB
  obtain ⟨q, hq, eq⟩ := exists_monic_map_eq_charpoly₂ C hC iC
  have hinj := IsFractionRing.injective K.O K.E
  have d1 : p ∣ f := (map_dvd_map _ hinj hp).1 (ep ▸ charpoly_dvd_map_of_aeval_eq_zero B hB f h0)
  have d2 : q ∣ 1 - f := (map_dvd_map _ hinj hq).1 (eq ▸ charpoly_dvd_map_of_aeval_eq_zero C hC (1 - f) (by simp [h1]))
  have hc : IsCoprime p q := by
    obtain ⟨a, ha⟩ := d1
    obtain ⟨b, hb⟩ := d2
    exact ⟨a, b, by linear_combination -ha - hb⟩
  rw [← ep, ← eq, resultant_map_map, natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj]
  exact val_unit _ ((isUnit_resultant_iff_isCoprime hp).2 hc)
end GlobalTheory.UnitLemma.Orbit
