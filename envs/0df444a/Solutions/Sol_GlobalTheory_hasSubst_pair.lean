-- Prove2me | solution 1 for GlobalTheory.hasSubst_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:53.775607+00:00
-- url     : https://prove2.me/submissions/bbac38c7-ed66-46f1-b337-4432105cd074

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SubstTwoVariablesIdentities

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
theorem _root_.solution {τ k : Type} [CommRing k] {z w : MvPowerSeries τ k}
    (hz : constantCoeff z = 0) (hw : constantCoeff w = 0) :
    HasSubst (![z, w] : Fin 2 → MvPowerSeries τ k) :=
  hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simpa
end GlobalTheory
