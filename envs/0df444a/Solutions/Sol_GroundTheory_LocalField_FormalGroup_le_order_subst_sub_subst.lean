-- Prove2me | solution 1 for GroundTheory.LocalField.FormalGroup.le_order_subst_sub_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:46:38.505802+00:00
-- url     : https://prove2.me/submissions/8401af24-0721-4583-9a66-28afc2856859

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsUniqueFixedPoint
import Definitions.Def_GroundTheory_LocalFields_FormalGroups_Truncation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open MvPowerSeries
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace GroundTheory.LocalField.FormalGroup
theorem _root_.solution {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f g : MvPowerSeries σ R} {n : ℕ∞}
    (h : n ≤ order (f - g)) : n ≤ order (subst a f - subst a g) := by
  rw [← subst_sub ha]
  refine le_trans ?_ (le_order_subst ha (f - g))
  have h1 : 1 ≤ ⨅ i, (a i).order :=
    le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha0 i)
  calc n ≤ 1 * order (f - g) := by simpa using h
    _ ≤ _ := by gcongr
end GroundTheory.LocalField.FormalGroup
