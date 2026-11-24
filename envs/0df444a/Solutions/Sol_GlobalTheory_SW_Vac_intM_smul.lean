-- Prove2me | solution 1 for GlobalTheory.SW.Vac.intM_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:56.437059+00:00
-- url     : https://prove2.me/submissions/8017cbab-f465-4e2a-94e3-2312dbe7ae47

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
omit [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution {x : Matrix κ ι ℚ} (n : ℕ) (h : IntM x) : IntM ((n : ℚ) • x) := by
  intro k i
  have := (h k i).nsmul n
  simpa [nsmul_eq_mul] using this
end GlobalTheory.SW.Vac
