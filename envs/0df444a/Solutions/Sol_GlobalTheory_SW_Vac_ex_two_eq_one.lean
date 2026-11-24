-- Prove2me | solution 1 for GlobalTheory.SW.Vac.ex_two_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:54.434263+00:00
-- url     : https://prove2.me/submissions/b71800dc-6e4e-4d29-81f2-bb871612bd5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution {r : ℚ} (h : ex (2 * r) = 1) : ∃ m : ℤ, r = m := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have : (r : ℂ) = n := by
    apply mul_right_cancel₀ h2
    rw [← hn]; push_cast; ring
  exact_mod_cast this
end GlobalTheory.SW.Vac
