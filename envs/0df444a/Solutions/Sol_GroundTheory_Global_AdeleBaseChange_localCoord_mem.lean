-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.localCoord_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:33.629752+00:00
-- url     : https://prove2.me/submissions/35381941-ae46-4f10-992a-dfdc3e9e02d8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_trace_mem_adicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_localCoord_eq_sum_trace

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
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (i : ι) (z : CompletionsOver L v)
    (hz : ∀ w : PlacesOver L v,
      z w * algebraMap L (w.1.adicCompletion L) (traceDual b i) ∈ w.1.adicCompletionIntegers L) :
    localCoord b v i z ∈ v.adicCompletionIntegers K := by
  rw [localCoord_eq_sum_trace]
  exact sum_mem fun w _ ↦ trace_mem_adicCompletionIntegers v w.1 (hz w)
end GroundTheory.Global.AdeleBaseChange
