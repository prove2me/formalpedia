-- Prove2me | solution 1 for GlobalTheory.Published.SvN.baer_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:08.689027+00:00
-- url     : https://prove2.me/submissions/beae6746-0127-424a-b017-e07355c69a33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}
namespace GlobalTheory.Published.SvN
theorem _root_.solution : Module.Baer ℤ (Additive ℂˣ) := by
  let : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn z => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact z.toMul.ne_zero (by rw [← hw, zero_pow hn])
    exact ⟨Additive.ofMul (Units.mk0 w hw0), Additive.toMul.injective (Units.ext (by simpa using hw))⟩
  let := AddGroup.divisibleByIntOfDivisibleByNat (Additive ℂˣ)
  exact Module.Baer.of_divisible _
end GlobalTheory.Published.SvN
