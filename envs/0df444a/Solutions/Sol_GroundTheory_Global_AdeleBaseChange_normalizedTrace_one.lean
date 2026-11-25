-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.normalizedTrace_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:26:38.71571+00:00
-- url     : https://prove2.me/submissions/4f89a8e6-0743-4ca9-b743-7996d8c1600a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange

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
theorem _root_.solution : normalizedTrace K L 1 = 1 := by
  rw [normalizedTrace, LinearMap.smul_apply, ← map_one (algebraMap K L), Algebra.trace_algebraMap,
    nsmul_eq_mul, mul_one, smul_eq_mul, inv_mul_cancel₀]
  exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
end GroundTheory.Global.AdeleBaseChange
