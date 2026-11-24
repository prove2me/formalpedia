-- Prove2me | solution 1 for GlobalTheory.SimMult.lift_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:46.605825+00:00
-- url     : https://prove2.me/submissions/60aa2b1c-fc6e-4894-91de-0c1240c32b51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult
import Theorems.Thm_GlobalTheory_SimMult_lift_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
variable {O : Type*} [CommRing O] (σ : O →+* O)
namespace GlobalTheory.SimMult
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) {w : O} (hw : w + σ w = 1) (I : Ideal O) (ν μ : ℤ)
    (hμ : (ν : O) * μ - 1 ∈ I) (c : O) (hc : c * σ c - ν ∈ I) (k : ℕ) :
    ∃ c', c' - c ∈ I ∧ c' * σ c' - ν ∈ I ^ k := by
  have key : ∀ k, ∃ c', c' - c ∈ I ∧ c' * σ c' - ν ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨c, by simp, by simpa using hc⟩
    | succ k ih =>
      obtain ⟨c₁, h1, h2⟩ := ih
      obtain ⟨c₂, h3, h4⟩ := lift_step σ hσ hw I ν μ hμ k c₁ h2
      exact ⟨c₂, by simpa using I.add_mem h3 h1, h4⟩
  obtain ⟨c', h1, h2⟩ := key k
  exact ⟨c', h1, Ideal.pow_le_pow_right (Nat.le_succ k) h2⟩
end GlobalTheory.SimMult
