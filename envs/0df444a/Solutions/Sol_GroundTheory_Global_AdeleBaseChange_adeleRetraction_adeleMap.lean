-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.adeleRetraction_adeleMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:23.537564+00:00
-- url     : https://prove2.me/submissions/199c300c-6be2-4674-b681-76f1ef10c096

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_traceRetraction_one_tmul
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_tmul


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
theorem _root_.solution (a : 𝔸[K]) : adeleRetraction K L (adeleMap K L a) = a := by
  have : (adeleTensorEquiv K L).symm (adeleMap K L a) = 1 ⊗ₜ a := by
    rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, one_mul]
  rw [adeleRetraction, this, traceRetraction_one_tmul]
end GroundTheory.Global.AdeleBaseChange
