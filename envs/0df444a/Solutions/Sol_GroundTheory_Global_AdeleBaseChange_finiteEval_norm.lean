-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.finiteEval_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:45:53.192973+00:00
-- url     : https://prove2.me/submissions/c1d347c0-e118-4d00-a349-747f26798be2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_completionsOverBasis_repr
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleBasis_repr


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
    finiteEval K v (Algebra.norm 𝔸[K] y) =
      Algebra.norm (v.adicCompletion K) (finiteRestrict L v y) := by
  classical
  refine (norm_map_of_repr (finiteEval K v) (finiteRestrict L v) (adeleBasis (Module.finBasis K L))
    (completionsOverBasis (Module.finBasis K L) v) (fun y i ↦ ?_) y).symm
  rw [completionsOverBasis_repr, adeleBasis_repr]
  rfl
end GroundTheory.Global.AdeleBaseChange
