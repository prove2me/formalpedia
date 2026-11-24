-- Prove2me | solution 1 for GlobalTheory.Div.QFibre.toQ_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:23:49.90438+00:00
-- url     : https://prove2.me/submissions/da630dca-7939-420e-a47c-b0b1a93a4cf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivFourierClassesPosConeSummand
import Theorems.Thm_GlobalTheory_SlopeTestRemainingChoices_EisFibre_rep_ne_zero


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
theorem _root_.solution (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by
  rintro ⟨β, ν, hν⟩ ⟨β', ν', hν'⟩ h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h
  simp only at h1 h2
  have hβ : β = β' := by
    rw [← Quotient.out_eq β, ← Quotient.out_eq β']
    exact Quotient.sound ⟨ε, h2⟩
  subst hβ
  have hε : ((ε : 𝓞 F) : F) = 1 := by
    have h0 := rep_ne_zero β
    have : (((ε : 𝓞 F) : F) - 1) * rep β = 0 := by unfold rep at h2 ⊢; rw [sub_mul, ← h2]; ring
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)
  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    have := unit_inv_mul ε; rw [hε, mul_one] at this; exact this
  rw [hε', one_mul] at h1
  have : (⟨ν, hν⟩ : posCone 𝔞 (rep β)) = ⟨ν', hν'⟩ := Subtype.ext h1.symm
  rw [this]
end GlobalTheory.Div.QFibre
