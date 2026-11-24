-- Prove2me | solution 1 for GlobalTheory.LatFibre.fibreMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:52:09.069226+00:00
-- url     : https://prove2.me/submissions/c79ae733-f037-4410-a303-220a9e6d308d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivLatticeClassesFibreSummand
import Theorems.Thm_GlobalTheory_LatFibre_unit_eq_one_of_mul
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
open GlobalTheory GlobalTheory.LatFibre
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LatFibre
theorem _root_.solution (𝔞 𝔟 : Frac F) : Function.Injective (fibreMap 𝔞 𝔟) := by
  rintro ⟨β, a⟩ ⟨β', a'⟩ h
  have h' : Quotient.mk (latRel 𝔞 𝔟) (pairOf ⟨β, a⟩) = Quotient.mk (latRel 𝔞 𝔟) (pairOf ⟨β', a'⟩) :=
    congrArg Subtype.val h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h'
  have hβ : β = β' :=
    (Quotient.out_eq (s := unitRel 𝔟) β).symm.trans
      ((Quotient.sound (s := unitRel 𝔟) (a := Quotient.out (s := unitRel 𝔟) β)
        (b := Quotient.out (s := unitRel 𝔟) β') ⟨ε, h2⟩).trans (Quotient.out_eq (s := unitRel 𝔟) β'))
  subst hβ
  have hε : ε = 1 := unit_eq_one_of_mul (rep_ne_zero β) h2.symm
  subst hε
  have haa : a = a' := Subtype.ext (by simpa [pairOf] using h1.symm)
  subst haa
  rfl
end GlobalTheory.LatFibre
