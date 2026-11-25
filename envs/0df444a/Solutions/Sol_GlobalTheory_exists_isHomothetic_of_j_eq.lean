-- Prove2me | solution 1 for GlobalTheory.exists_isHomothetic_of_j_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:09.507926+00:00
-- url     : https://prove2.me/submissions/2ac9d1db-0a0b-4e90-845f-a7f8ce192a78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Theorems.Thm_P2M_GlobalTheory_lattice_eq_of_g__eq_of_g__eq_399c7fadf18d
import Theorems.Thm_P2M_GlobalTheory_g__cube_sub_g__sq_ne_zero_9f5991ca482c
import Theorems.Thm_P2M_GlobalTheory_IsHomothetic_g__eq_dbfeb170147e
import Theorems.Thm_P2M_GlobalTheory_IsHomothetic_g__eq_8571fef95872
import Theorems.Thm_GlobalTheory_exists_scale_of_j_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology Real UpperHalfPlane
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {L L' : PeriodPair}
    (e : L.g₂ ^ 3 * (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) = L'.g₂ ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) :
    ∃ c : ℂ, IsHomothetic c L L' := by
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq (g₂_cube_sub_g₃_sq_ne_zero L)
    (g₂_cube_sub_g₃_sq_ne_zero L') e
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hu (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  have : (scalePeriods L c hc0).lattice = L'.lattice := by
    refine lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_
    · rw [H.g₂_eq, h2, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; simp
    · rw [H.g₃_eq, h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; simp
  exact ⟨c, fun x ↦ this ▸ H x⟩
end GlobalTheory
