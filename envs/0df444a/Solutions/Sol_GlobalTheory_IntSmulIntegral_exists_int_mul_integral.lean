-- Prove2me | solution 1 for GlobalTheory.IntSmulIntegral.exists_int_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:47:53.208571+00:00
-- url     : https://prove2.me/submissions/38058726-8f55-4453-80a3-a12e8572eb13

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntSmulIntegral
open NumberField
namespace GlobalTheory.IntSmulIntegral
theorem _root_.solution {K : Type} [Field K] [NumberField K] (a : K) :
    ∃ (m : ℤ) (z : 𝓞 K), m ≠ 0 ∧ (z : K) = m • a := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  obtain ⟨m, hm, hint⟩ := ((Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic ℚ a).restrictScalars ℤ).exists_integral_multiple
  exact ⟨m, ⟨m • a, hint⟩, hm, rfl⟩
end GlobalTheory.IntSmulIntegral
