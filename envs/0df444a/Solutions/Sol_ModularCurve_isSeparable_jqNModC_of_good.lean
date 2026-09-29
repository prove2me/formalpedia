-- Prove2me | solution 1 for ModularCurve.isSeparable_jqNModC_of_good
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a4099a7b-7c32-5fb2-a624-6f03449b3994

import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_separable_phi_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isSeparable_jqNModC_of_good
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
open ModularCurve
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (hℓN : ¬ ℓ ∣ N) :
    IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hNK : (N : K) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff K ℓ N).mp h)
  exact isSeparable_jqNModC_of_separable_phi_map K N data
    (ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero K N data hNK)

end S_ModularCurve_isSeparable_jqNModC_of_good
end P2MW
export P2MW.S_ModularCurve_isSeparable_jqNModC_of_good (solution)
