-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.traceRetraction_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:38:37.016557+00:00
-- url     : https://prove2.me/submissions/b338db69-3af5-449a-9efb-130dc313ce4b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_normalizedTrace_one

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
theorem _root_.solution (a : 𝔸[K]) : traceRetraction K L (1 ⊗ₜ a) = a := by
  change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) (1 ⊗ₜ a)) = a
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, normalizedTrace_one, one_smul]
end GroundTheory.Global.AdeleBaseChange
