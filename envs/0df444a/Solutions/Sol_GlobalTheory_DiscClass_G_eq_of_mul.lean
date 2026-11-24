-- Prove2me | solution 1 for GlobalTheory.DiscClass.G_eq_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:23:45.011154+00:00
-- url     : https://prove2.me/submissions/23f63b92-03c6-414c-a20a-af5ba2dfecd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealNormPowSixMulDiscriminantClassInv
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
theorem _root_.solution (Λ Λ' : PeriodPair) (u : ℂ) (hu : u ≠ 0) (h : ∀ w, u * w ∈ Λ'.lattice ↔ w ∈ Λ.lattice) (k : ℕ) :
    Λ.G k = u ^ k * Λ'.G k := by
  let e : (Λ.lattice : Set ℂ) ≃ (Λ'.lattice : Set ℂ) :=
    (Equiv.mulLeft₀ u hu).subtypeEquiv fun w => by simpa using (h w).symm
  have h2 : ∀ P : PeriodPair, P.G k = ∑' w : (P.lattice : Set ℂ), ((w : ℂ) ^ k)⁻¹ := fun _ => rfl
  rw [h2, h2, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun w => ?_
  have : ((e w : (Λ'.lattice : Set ℂ)) : ℂ) = u * w := rfl
  rw [this, mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), one_mul]
end GlobalTheory.DiscClass
