-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.finiteTensorHomeomorph_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:52.342418+00:00
-- url     : https://prove2.me/submissions/abe904ed-1363-4fbb-ba40-f0e56e1d7584

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
theorem _root_.solution (t : L ⊗[K] FiniteAdeleRing (𝓞 K) K) :
    finiteTensorHomeomorph K L t = finiteTensorEquiv K L t :=
  rfl
end GroundTheory.Global.AdeleBaseChange
