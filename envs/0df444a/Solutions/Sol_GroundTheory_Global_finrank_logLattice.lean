-- Prove2me | solution 1 for GroundTheory.Global.finrank_logLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:39.394298+00:00
-- url     : https://prove2.me/submissions/fa268bba-ec28-428d-b6d2-3ba82f74fa64

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
import Theorems.Thm_GroundTheory_Global_SUnit_finrank_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
  MulAction Module
open scoped TensorProduct
noncomputable section
open scoped Classical
variable (L : Type*) [Field L] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution : finrank ℤ (logLattice L) = rank L :=
  (logLatticeEquiv L).finrank_eq.trans (unitLattice_rank L)
end GroundTheory.Global
