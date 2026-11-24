-- Prove2me | solution 1 for GlobalTheory.PolModLattice.trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:36.541005+00:00
-- url     : https://prove2.me/submissions/84797c0b-d64a-4413-9812-6d905674485a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
import Theorems.Thm_GlobalTheory_PolModLattice_univ_aut
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
theorem _root_.solution (u : E) (w : maximalRealSubfield E) (hw : (w : E) = u + bar u) :
    Algebra.trace ℚ E u = Algebra.trace ℚ (maximalRealSubfield E) w := by
  rw [← Algebra.trace_trace (S := maximalRealSubfield E)]
  congr 1
  apply FaithfulSMul.algebraMap_injective (maximalRealSubfield E) E
  classical
  rw [trace_eq_sum_automorphisms, univ_aut, Finset.sum_pair (Ne.symm (IsCMField.complexConj_ne_one E))]
  simp only [AlgEquiv.one_apply]
  exact hw.symm
end GlobalTheory.PolModLattice
