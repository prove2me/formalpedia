-- Prove2me | solution 1 for GroundTheory.Global.ideleNorm_ideleEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:14:43.88879+00:00
-- url     : https://prove2.me/submissions/37ddaf12-8222-4663-bf92-c3695ccbb42d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_norm_adeleRing_adeleMap

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
open AdeleBaseChange
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {K L}
namespace GroundTheory.Global
theorem _root_.solution (x : IdeleGroup K) :
    ideleNorm K L (ideleEmbedding K L x) = x ^ Module.finrank K L :=
  Units.ext (by rw [Units.val_pow_eq_pow_val]; exact norm_adeleRing_adeleMap (x : 𝔸[K]))
end GroundTheory.Global
