-- Prove2me | solution 1 for GlobalTheory.SW.HaarAlg.intM_natCast_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:56.910546+00:00
-- url     : https://prove2.me/submissions/be3f6b0a-4643-4e6c-b665-6d374a4dd09e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarAlg
variable {K : Type} [Field K] {κ ι : Type}
namespace GlobalTheory.SW.HaarAlg
theorem _root_.solution (n : ℕ) {x : Matrix κ ι K} (hx : IntM x) : IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul, ← nsmul_eq_mul]
  exact (hx k i).nsmul n
end GlobalTheory.SW.HaarAlg
