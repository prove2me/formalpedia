-- Prove2me | solution 1 for GlobalTheory.SW.HaarAlg.intM_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:25:58.926258+00:00
-- url     : https://prove2.me/submissions/02bfecb0-c201-43e8-bfa5-bca125a8456a

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
theorem _root_.solution {x y : Matrix κ ι K} (hx : IntM x) (hy : IntM y) : IntM (x + y) :=
  fun k i => (hx k i).add (hy k i)
end GlobalTheory.SW.HaarAlg
