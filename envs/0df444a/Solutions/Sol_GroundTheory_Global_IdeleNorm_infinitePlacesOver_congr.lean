-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.infinitePlacesOver_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:53.559518+00:00
-- url     : https://prove2.me/submissions/9fac5aec-388e-481e-a8e3-551f23465656

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms

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
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]
variable {L}
omit [NumberField K] [NumberField L]
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (yi : ∀ v : InfinitePlace K,
      (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    {v v' : InfinitePlace K} (h : v' = v) (w : InfinitePlace L)
    (hw : w ∈ v.placesOver L) (hw' : w ∈ v'.placesOver L) :
    yi v' ⟨w, hw'⟩ = yi v ⟨w, hw⟩ := by
  subst h
  rfl
end GroundTheory.Global.IdeleNorm
