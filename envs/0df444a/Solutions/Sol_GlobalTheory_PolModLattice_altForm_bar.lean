-- Prove2me | solution 1 for GlobalTheory.PolModLattice.altForm_bar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:43.233285+00:00
-- url     : https://prove2.me/submissions/a978bbd1-af39-4027-ae0f-ad72e8fa3c41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
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
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PolModLattice
theorem _root_.solution (x y : E) : bar (altForm x y) = - altForm x y := by
  simp only [altForm, bar, map_sub, map_mul, IsCMField.complexConj_apply_apply]; ring
end GlobalTheory.PolModLattice
