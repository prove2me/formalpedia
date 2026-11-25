-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.glue_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:23.590938+00:00
-- url     : https://prove2.me/submissions/bfcf500d-67bc-4b20-80fb-f3e49f5e9691

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Theorems.Thm_GroundTheory_Global_IdeleNorm_infinitePlacesOver_congr
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst



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
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    (v : InfinitePlace K) (w : v.placesOver L) :
    ((glue yf hyf yi : 𝔸[L]).1 w) = (yi v w : (w : InfinitePlace L).Completion) := by
  rw [← IdeleGroup.prodRestrictedEquiv_apply_fst, glue, ContinuousMulEquiv.apply_symm_apply]
  have := infinitePlacesOver_congr yi (InfinitePlace.LiesOver.comap_eq (w : InfinitePlace L) v)
    (w : InfinitePlace L) w.2
    (inferInstance : (w : InfinitePlace L).LiesOver ((w : InfinitePlace L).comap (algebraMap K L)))
  exact congrArg Units.val this
end GroundTheory.Global.IdeleNorm
