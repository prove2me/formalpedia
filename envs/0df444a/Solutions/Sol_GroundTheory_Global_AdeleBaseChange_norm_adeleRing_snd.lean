-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.norm_adeleRing_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:32.133378+00:00
-- url     : https://prove2.me/submissions/5b13f05a-9c41-41ef-aa92-97a49228a871

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteEval_norm
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
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).2 v =
      ∏ w : PlacesOver L v, Algebra.norm (v.adicCompletion K) (y.2 w.1) :=
  (finiteEval_norm v y).trans (norm_pi _)
end GroundTheory.Global.AdeleBaseChange
