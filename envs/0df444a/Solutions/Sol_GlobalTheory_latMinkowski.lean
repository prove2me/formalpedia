-- Prove2me | solution 1 for GlobalTheory.latMinkowski
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:31:52.384479+00:00
-- url     : https://prove2.me/submissions/3e4afc96-b76f-4623-8879-a2d2e7939624

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Theorems.Thm_GlobalTheory_end_eq_one_of_pow_eq_one_of_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LatMinkowskiSt := by
  intro Y _ _ _ σ n M hn hσ hM h
  have hp : (σ : Module.End ℤ Y) ^ n = 1 := by
    ext y
    have : (σ ^ n) y = y := by rw [hσ]; rfl
    rw [LinearEquiv.pow_apply] at this
    rw [Module.End.pow_apply]
    exact this
  have := end_eq_one_of_pow_eq_one_of_congr Y (σ : Module.End ℤ Y) n M hn hp hM h
  ext y
  exact LinearMap.congr_fun this y
end GlobalTheory
