-- Prove2me | solution 1 for GlobalTheory.SW.Vac.pr_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:48:24.129795+00:00
-- url     : https://prove2.me/submissions/67447d5c-7ab4-41c2-82f7-2fe8022bfbe0

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
theorem _root_.solution {x a : Matrix κ ι ℚ} (hx : IntM x) (ha : IntM a) : ∃ m : ℤ, pr x a = m := by
  have : IsIntegral ℤ (pr x a) := by
    unfold pr dotProduct
    exact IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => (hx k i).mul (ha k i)
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 this
  exact ⟨m, by simpa using hm.symm⟩
end GlobalTheory.SW.Vac
