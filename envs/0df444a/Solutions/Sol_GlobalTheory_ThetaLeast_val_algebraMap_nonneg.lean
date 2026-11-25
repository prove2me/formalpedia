-- Prove2me | solution 1 for GlobalTheory.ThetaLeast.val_algebraMap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:49.328255+00:00
-- url     : https://prove2.me/submissions/28c024f6-5f68-4748-8d08-398661665ba4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCombinationIntegers
import Theorems.Thm_GlobalTheory_vV_algebraMap_nonneg_dvr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.ThetaLeast
namespace GlobalTheory.ThetaLeast
theorem _root_.solution (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ)) (x : T.V) :
    0 ≤ v (algebraMap T.Fr F (algebraMap T.V T.Fr x)) := by
  by_cases hx : algebraMap T.V T.Fr x = 0
  · rw [hx, map_zero, AddValuation.map_zero]; exact le_top
  · rw [hv _ hx]
    exact_mod_cast GlobalTheory.vV_algebraMap_nonneg_dvr T x
end GlobalTheory.ThetaLeast
