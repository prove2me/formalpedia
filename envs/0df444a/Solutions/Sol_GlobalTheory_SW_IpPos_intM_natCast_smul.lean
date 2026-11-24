-- Prove2me | solution 1 for GlobalTheory.SW.IpPos.intM_natCast_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:11.100802+00:00
-- url     : https://prove2.me/submissions/0783e51a-6c7a-410f-b9f1-b05b57820b93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.IpPos
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
open Matrix Complex
open scoped ComplexConjugate Real
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
omit [NumberField K] [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.IpPos
namespace _root_.GlobalTheory.SW.IpPos
theorem _root_.solution (n : ℕ) {x : Matrix κ ι K}
    (hx : _root_.GlobalTheory.SW.IntM x) : _root_.GlobalTheory.SW.IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isIntegral_natCast n).mul (hx k i)
end _root_.GlobalTheory.SW.IpPos
end GlobalTheory.SW.IpPos
