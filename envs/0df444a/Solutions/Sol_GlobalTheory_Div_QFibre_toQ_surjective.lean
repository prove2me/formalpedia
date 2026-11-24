-- Prove2me | solution 1 for GlobalTheory.Div.QFibre.toQ_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:43:04.280747+00:00
-- url     : https://prove2.me/submissions/5489b9d5-f37d-41b0-bbaa-ce03e3931cb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivFourierClassesPosConeSummand
import Theorems.Thm_GlobalTheory_Div_QFibre_unit_mul_mem
import Theorems.Thm_GlobalTheory_Div_QFibre_exists_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.QFibre
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.Div.QFibre
theorem _root_.solution [IsTotallyReal F] (𝔞 𝔟 : Frac F) : Function.Surjective (toQ 𝔞 𝔟) := by
  intro c
  induction c using Quotient.ind with
  | _ p =>
  obtain ⟨⟨ν, b⟩, hν, hb, hpos⟩ := p
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨τ⟩ := exists_emb (F := F)
    have := hpos τ; simp at this
  let β : NzCls 𝔟 := Quotient.mk _ ⟨b, hb, hb0⟩
  obtain ⟨ε, hε⟩ : (unitRel 𝔟).r (Quotient.out β) ⟨b, hb, hb0⟩ := Quotient.exact (Quotient.out_eq β)
  have h4 := unit_inv_mul ε
  have hrep : rep β = (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * b := by
    unfold rep; simp only at hε; rw [hε, ← mul_assoc, h4, one_mul]
  have hprod : ((ε : 𝓞 F) : F) * ν * rep β = ν * b := by
    rw [hrep]; linear_combination (ν * b) * h4
  refine ⟨⟨β, ((ε : 𝓞 F) : F) * ν, unit_mul_mem 𝔞 ε hν, fun τ => by rw [hprod]; exact hpos τ⟩, ?_⟩
  apply Quotient.sound
  refine ⟨ε, ?_, ?_⟩
  · show ν = _ * (((ε : 𝓞 F) : F) * ν)
    rw [← mul_assoc, h4, one_mul]
  · show b = ((ε : 𝓞 F) : F) * rep β
    rw [hrep, ← mul_assoc, mul_comm ((ε : 𝓞 F) : F), h4, one_mul]
end GlobalTheory.Div.QFibre
