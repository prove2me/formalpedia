-- Prove2me | solution 1 for GlobalTheory.LatFibre.fibreMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:37:30.265898+00:00
-- url     : https://prove2.me/submissions/582cf3fc-c7d4-495b-8fe5-b9df7028983d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivLatticeClassesFibreSummand

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
theorem _root_.solution (𝔞 𝔟 : Frac F) : Function.Surjective (fibreMap 𝔞 𝔟) := by
  rintro ⟨c, hc⟩
  let b : NzElt 𝔟 := ⟨c.out.1.2, c.out.2.2.1, hc⟩
  obtain ⟨ε, hε⟩ : ∃ ε : (𝓞 F)ˣ,
      rep (Quotient.mk (unitRel 𝔟) b : NzCls 𝔟) = ((ε : 𝓞 F) : F) * c.out.1.2 :=
    Quotient.exact (Quotient.out_eq (Quotient.mk (unitRel 𝔟) b)).symm
  have ha : ((ε : 𝓞 F) : F) * c.out.1.1 ∈ latM 𝔞 := by
    have hs := (latM 𝔞 : Submodule (𝓞 F) F).smul_mem (ε : 𝓞 F) c.out.2.1
    rwa [Algebra.smul_def] at hs
  refine ⟨⟨(Quotient.mk (unitRel 𝔟) b : NzCls 𝔟), ⟨_, ha⟩⟩, ?_⟩
  apply Subtype.ext
  show Quotient.mk (latRel 𝔞 𝔟) (pairOf _) = c
  conv_rhs => rw [← Quotient.out_eq c]
  exact (Quotient.sound (s := latRel 𝔞 𝔟) (a := c.out) ⟨ε, rfl, hε⟩).symm
end GlobalTheory.LatFibre
