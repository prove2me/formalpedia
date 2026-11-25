-- Prove2me | solution 1 for GlobalTheory.lattice_determined_by_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:52.620707+00:00
-- url     : https://prove2.me/submissions/80d74bc8-b742-4db1-a519-8758332bbb6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Theorems.Thm_P2M_GlobalTheory_lattice_eq_of_g__eq_of_g__eq_399c7fadf18d
import Theorems.Thm_GlobalTheory_exists_isHomothetic_of_j_eq

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
theorem _root_.solution (L L' : PeriodPair) :
    (L.g₂ = L'.g₂ → L.g₃ = L'.g₃ → L.lattice = L'.lattice) ∧
    (L.g₂ ^ 3 * (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) = L'.g₂ ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ w ∈ L.lattice, z = c * w) := by
  refine ⟨lattice_eq_of_g₂_eq_of_g₃_eq, fun e ↦ ?_⟩
  obtain ⟨c, h⟩ := exists_isHomothetic_of_j_eq e
  refine ⟨c, h.ne_zero, fun z ↦ ⟨fun hz ↦ ⟨c⁻¹ * z, (h _).1 (by simpa [h.ne_zero] using hz),
    by simp [h.ne_zero]⟩, ?_⟩⟩
  rintro ⟨w, hw, rfl⟩
  exact (h w).2 hw
end GlobalTheory
