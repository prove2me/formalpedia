-- Prove2me | solution 1 for GroundTheory.Global.Artin.fixedFieldMulEquiv_smul_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:16:58.492337+00:00
-- url     : https://prove2.me/submissions/9e2a89e6-94e5-4dcb-8b35-55078e045ddb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesInfinite
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
omit [IsGalois K L]
namespace GroundTheory.Global.Artin
theorem _root_.solution (h : H) (P : Ideal (𝓞 L)) :
    fixedFieldMulEquiv H h • P = h • P := by
  rw [Ideal.pointwise_smul_def]
  change _ = (h : Gal(L/K)) • P
  rw [Ideal.pointwise_smul_def]
  rfl
end GroundTheory.Global.Artin
