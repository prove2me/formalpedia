-- Prove2me | solution 1 for GlobalTheory.DerivAtOrigin.zero_mem_polydisc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:10.924906+00:00
-- url     : https://prove2.me/submissions/847b4572-c8bf-4beb-8964-841f49923249

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
theorem _root_.solution (I : Type) : (0 : I → ℂ) ∈ polydisc I := by
  intro i; simp
end GlobalTheory.DerivAtOrigin
