-- Prove2me | solution 1 for GroundTheory.Global.logLatticeProdMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:10.70245+00:00
-- url     : https://prove2.me/submissions/9a9393b8-481c-4346-98ea-336b6894efc8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue

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
open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
omit [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution (m : logLattice L) (n : ℤ) :
    logLatticeProdMap (m, n) = (m : InfinitePlace L → ℝ) + n • (1 : InfinitePlace L → ℝ) :=
  rfl
end GroundTheory.Global
