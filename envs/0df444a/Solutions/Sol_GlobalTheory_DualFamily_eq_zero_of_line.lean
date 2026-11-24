-- Prove2me | solution 1 for GlobalTheory.DualFamily.eq_zero_of_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:24:52.746906+00:00
-- url     : https://prove2.me/submissions/37ea0ef0-c8dd-427f-a376-36e4f738297e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.DualFamily
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.DualFamily
namespace _root_.GlobalTheory.DualFamily
theorem _root_.solution {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (w : Fin n → E) (hw : ∀ c : E, c • w ∈ Λ) : w = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  have htop : Λ.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) j) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ⟨(x / w j) • w, hw _, ?_⟩
    simp [div_mul_cancel₀ _ hj]
  have : Module.Finite (𝓞 E) E := ⟨by rw [← htop]; exact hfg.map _⟩
  have := Algebra.IsIntegral.of_finite (𝓞 E) E
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
end _root_.GlobalTheory.DualFamily
end GlobalTheory.DualFamily
