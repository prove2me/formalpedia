-- Prove2me | solution 1 for ModularCurve.map_jqNModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/fc9dbaf5-3058-50c3-8a29-46c6e0db9fd9

import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_map_jqNModC

p2m_open "ModularCurve P2MW.S_ModularCurve_map_jqNModC.ModularCurve"

set_option autoImplicit false

namespace ModularCurve p2m_export "ModularCurve" "coeffMap coeffMap_coeff jqModC jqNModC map_jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.solution_aux_coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (N : ℕ) [NeZero N] : coeffMap φ (jqNModC R N) = jqNModC S N := by
  have hj : coeffMap φ (jqModC R) = jqModC S := map_jqModC φ
  rw [jqNModC, jqNModC, ModularCurve.solution_aux_coeffMap_qExpand, hj]

end S_ModularCurve_map_jqNModC
end P2MW
export P2MW.S_ModularCurve_map_jqNModC (solution)
