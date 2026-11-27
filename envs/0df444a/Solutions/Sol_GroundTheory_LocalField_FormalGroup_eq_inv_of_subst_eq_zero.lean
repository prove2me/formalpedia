-- Prove2me | solution 1 for GroundTheory.LocalField.FormalGroup.eq_inv_of_subst_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:46:36.520572+00:00
-- url     : https://prove2.me/submissions/cc656f85-23ca-472a-96a7-e3a95f328bd2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FormalGroups_Truncation
import Definitions.Def_GroundTheory_LocalFields_FormalGroups_Inverse

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
variable {R : Type*} [CommRing R] (F : FormalGroup R)
namespace GroundTheory.LocalField.FormalGroup
theorem _root_.solution {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (h : subst ![PowerSeries.X, g] F.toPowerSeries = (0 : PowerSeries R)) : g = inv F := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have hg' : constantCoeff (g : MvPowerSeries Unit R) = 0 := hg
  change subst ![X (), (g : MvPowerSeries Unit R)] F.toPowerSeries = 0 at h
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hX hg')] at h
  have hfix : invStep F g = g := by
    rw [invStep_of_constantCoeff_eq_zero F hg']
    linear_combination (-1 : MvPowerSeries Unit R) * h
  exact (existsUnique_invStep F).unique hfix (invStep_inv F)
end GroundTheory.LocalField.FormalGroup
