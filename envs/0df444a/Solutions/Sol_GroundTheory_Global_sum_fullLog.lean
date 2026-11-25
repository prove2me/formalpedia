-- Prove2me | solution 1 for GroundTheory.Global.sum_fullLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:05:26.269737+00:00
-- url     : https://prove2.me/submissions/32dc5a47-0021-4e84-9074-0c2236ebda7e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand

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
theorem _root_.solution (x : Additive (𝓞 L)ˣ) : ∑ w, fullLog L x w = 0 :=
  sum_mult_mul_log x.toMul
end GroundTheory.Global
