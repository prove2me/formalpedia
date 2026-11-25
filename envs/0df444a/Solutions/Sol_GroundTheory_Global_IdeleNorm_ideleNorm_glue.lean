-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.ideleNorm_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:03.542778+00:00
-- url     : https://prove2.me/submissions/b7a66a0c-9c93-4ef8-a315-34dbd7bf702a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
import Theorems.Thm_GroundTheory_Global_IdeleNorm_coe_finiteLocalNorm
import Theorems.Thm_GroundTheory_Global_IdeleNorm_coe_infiniteLocalNorm
import Theorems.Thm_GroundTheory_Global_IdeleNorm_glue_snd
import Theorems.Thm_GroundTheory_Global_IdeleNorm_glue_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_ideleNorm_fst
import Theorems.Thm_GroundTheory_Global_ideleNorm_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj



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
    {x : IdeleGroup K} (hf : ∀ v, finiteLocalNorm L v (yf v) = IdeleGroup.finiteProj v x)
    (hi : ∀ v, infiniteLocalNorm L v (yi v) = IdeleGroup.infiniteProj v x) :
    ideleNorm K L (glue yf hyf yi) = x := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun v ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst, ← IdeleGroup.coe_infiniteProj, ← hi v, coe_infiniteLocalNorm]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [glue_fst]
  · rw [ideleNorm_snd, ← IdeleGroup.coe_finiteProj, ← hf v, coe_finiteLocalNorm]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [glue_snd]
end GroundTheory.Global.IdeleNorm
