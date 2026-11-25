-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.norm_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:24:06.619176+00:00
-- url     : https://prove2.me/submissions/25e0d2a5-4d0f-4419-9edc-99f393cb638d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound

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
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (k : Kˣ) (y : IdeleGroup K) (w : InfinitePlace K) :
    ‖((diagonal K k * y : IdeleGroup K) : 𝔸[K]).1 w‖ = w (k : K) * ‖(y : 𝔸[K]).1 w‖ := by
  rw [Units.val_mul, adele_fst_mul_apply, norm_mul]
  congr 1
  exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _
end GroundTheory.Global.IdeleGroup
