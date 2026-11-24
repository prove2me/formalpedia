-- Prove2me | solution 1 for GlobalTheory.CMExtend.ringHom_ext_orderC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:03:56.425422+00:00
-- url     : https://prove2.me/submissions/24a5654d-602f-4184-9f5a-9be799871d75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodNormIntegral
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
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.CMExtend
variable {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)}
variable {K A : Type} [Field K] [CharZero K] [Ring A] [Algebra K A]
namespace GlobalTheory.CMExtend
theorem _root_.solution (hc : c ≠ ⊥) {B : Type} [Ring B] (f₁ f₂ : E →+* B) (h : ∀ a : orderC c, f₁ a = f₂ a) :
    f₁ = f₂ := by
  ext x
  obtain ⟨n, hn, hnx⟩ := exists_natMul_mem_orderC hc x
  have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : f₁ ((n : E)⁻¹) * (n : B) = 1 := by
    rw [← map_natCast f₁, ← map_mul, inv_mul_cancel₀ hnE, map_one]
  have h2 : (n : B) * f₂ ((n : E)⁻¹) = 1 := by
    rw [← map_natCast f₂, ← map_mul, mul_inv_cancel₀ hnE, map_one]
  have hinv : f₁ ((n : E)⁻¹) = f₂ ((n : E)⁻¹) := by
    calc f₁ ((n : E)⁻¹) = f₁ ((n : E)⁻¹) * ((n : B) * f₂ ((n : E)⁻¹)) := by rw [h2, mul_one]
      _ = f₂ ((n : E)⁻¹) := by rw [← mul_assoc, h1, one_mul]
  have hx : x = (n : E)⁻¹ * ((n : E) * x) := by rw [← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
  have := h ⟨(n : E) * x, hnx⟩
  simp only at this
  calc f₁ x = f₁ ((n : E)⁻¹ * ((n : E) * x)) := congrArg f₁ hx
    _ = f₂ ((n : E)⁻¹ * ((n : E) * x)) := by rw [map_mul f₁, hinv, this, ← map_mul]
    _ = f₂ x := (congrArg f₂ hx).symm
end GlobalTheory.CMExtend
