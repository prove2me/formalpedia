-- Prove2me | solution 1 for GlobalTheory.invariants_of_periods_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:43.282623+00:00
-- url     : https://prove2.me/submissions/32b23a3a-7161-4d21-ac2f-aa86b5bfe9c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Theorems.Thm_P2M_GlobalTheory_g__cube_sub_g__sq_eq_discriminant_b8dac546ba0a
import Theorems.Thm_P2M_GlobalTheory_g__cube_sub_g__sq_eq_eta_50875d2c00b3
import Theorems.Thm_P2M_GlobalTheory_g__cube_div_eq_modularJ_a1bc96193403
import Theorems.Thm_GlobalTheory_mem_lattice_iff_of_periods_eq

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
theorem _root_.solution {L : PeriodPair} {τ : ℍ}
    (h : (L.ω₁ = 1 ∧ L.ω₂ = τ) ∨ (L.ω₁ = τ ∧ L.ω₂ = 1)) :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π) ^ 12 * ModularForm.discriminant τ ∧
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π) ^ 12 * ModularForm.eta τ ^ 24 ∧
    1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = modularJ τ :=
  ⟨by simpa using g₂_cube_sub_g₃_sq_eq_discriminant one_ne_zero (mem_lattice_iff_of_periods_eq h),
    by simpa using g₂_cube_sub_g₃_sq_eq_eta one_ne_zero (mem_lattice_iff_of_periods_eq h),
    g₂_cube_div_eq_modularJ one_ne_zero (mem_lattice_iff_of_periods_eq h)⟩
end GlobalTheory
