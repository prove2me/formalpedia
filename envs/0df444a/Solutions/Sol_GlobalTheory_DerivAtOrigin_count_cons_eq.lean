-- Prove2me | solution 1 for GlobalTheory.DerivAtOrigin.count_cons_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:36.220338+00:00
-- url     : https://prove2.me/submissions/f527b427-76b2-45ac-af48-b954616dcd4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivFormulaOfSeries
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DerivAtOrigin
namespace GlobalTheory.DerivAtOrigin
theorem _root_.solution {I : Type} [DecidableEq I] (i : I) (l : List I) :
    (fun j => (i :: l).count j) = (fun j => l.count j) + Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [List.count_cons]
  · simp [List.count_cons, Pi.single_apply, h, Ne.symm h]
end GlobalTheory.DerivAtOrigin
