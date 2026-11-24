-- Prove2me | solution 1 for GlobalTheory.DiscClass.latDisc_eq_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:43:01.696869+00:00
-- url     : https://prove2.me/submissions/7daa2df6-eab1-4cae-a7e1-8f09ab262e24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealNormPowSixMulDiscriminantClassInv
import Theorems.Thm_GlobalTheory_DiscClass_G_eq_of_mul
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
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DiscClass
namespace GlobalTheory.DiscClass
theorem _root_.solution (Λ Λ' : PeriodPair) (u : ℂ) (hu : u ≠ 0) (h : ∀ w, u * w ∈ Λ'.lattice ↔ w ∈ Λ.lattice) :
    latDisc Λ = u ^ 12 * latDisc Λ' := by
  simp only [latDisc, PeriodPair.g₂, PeriodPair.g₃, G_eq_of_mul Λ Λ' u hu h 4, G_eq_of_mul Λ Λ' u hu h 6]
  ring
end GlobalTheory.DiscClass
