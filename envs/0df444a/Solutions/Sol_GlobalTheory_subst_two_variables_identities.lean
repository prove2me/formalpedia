-- Prove2me | solution 1 for GlobalTheory.subst_two_variables_identities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:20.342886+00:00
-- url     : https://prove2.me/submissions/7bdb2c33-b7c5-43ad-bef2-64522a780f1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SubstTwoVariablesIdentities
import Theorems.Thm_GlobalTheory_hasSubst_pair
import Theorems.Thm_GlobalTheory_subst_pair_subst_X
import Theorems.Thm_GlobalTheory_subst_pair_subst_shear
import Theorems.Thm_GlobalTheory_X_one_dvd_iff_subst_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPowerSeries
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k], (∀ h : MvPowerSeries (Fin 2) k, (MvPowerSeries.X 1 ∣ MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h ↔ MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) h = 0) ∧ ∀ z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) = MvPowerSeries.subst (![z, z + w] : Fin 2 → PowerSeries k) h) ∧ ∀ x z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)) = x.subst z ∧ MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)) = x.subst w := by
  intro k _
  refine ⟨fun h => ⟨?_, fun z w hz hw => subst_pair_subst_shear h hz hw⟩, fun x z w hz hw =>
    ⟨subst_pair_subst_X x 0 (hasSubst_pair hz hw), subst_pair_subst_X x 1 (hasSubst_pair hz hw)⟩⟩
  rw [X_one_dvd_iff_subst_eq_zero,
    subst_pair_subst_shear h PowerSeries.constantCoeff_X (map_zero _), add_zero]
end GlobalTheory
