-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.glue_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:46.613455+00:00
-- url     : https://prove2.me/submissions/1d34ecba-7ed3-4f40-b6fe-919c90b5aaa1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Theorems.Thm_GroundTheory_Global_IdeleNorm_placesOver_congr
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd



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
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) :
    ((glue yf hyf yi : 𝔸[L]).2 w.1) = (yf v w : w.1.adicCompletion L) := by
  rw [← IdeleGroup.prodRestrictedEquiv_apply_snd, glue, ContinuousMulEquiv.apply_symm_apply]
  exact congrArg Units.val (placesOver_congr yf ((below_eq_iff w.1 v).2 w.2) w.1 w.2 _)
end GroundTheory.Global.IdeleNorm
