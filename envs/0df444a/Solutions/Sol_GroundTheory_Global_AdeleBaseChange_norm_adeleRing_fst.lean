-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.norm_adeleRing_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:45.483016+00:00
-- url     : https://prove2.me/submissions/f8979cec-7ac4-4ec5-a289-60d6ef743776

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_infiniteEval_norm
import Theorems.Thm_GroundTheory_Global_Algebra_norm_pi
import Theorems.Thm_GroundTheory_Global_SemiLocal_norm_pi


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
open IsDedekindDomain NumberField TensorProduct Module
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
open scoped Classical
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (v : InfinitePlace K) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (y.1 w) :=
  (infiniteEval_norm v y).trans (GroundTheory.Global.Algebra.norm_pi _)
end GroundTheory.Global.AdeleBaseChange
