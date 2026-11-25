-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.adeleMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:20:28.876402+00:00
-- url     : https://prove2.me/submissions/8a111878-5d8b-4f9f-b7f4-4f9de44608e0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleRetraction_adeleMap

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
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution : Function.Injective (adeleMap K L) :=
  Function.LeftInverse.injective (g := adeleRetraction K L) adeleRetraction_adeleMap
end GroundTheory.Global.AdeleBaseChange
