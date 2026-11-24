-- Prove2me | solution 1 for GlobalTheory.SW.HaarAlg.finsum_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:16.611793+00:00
-- url     : https://prove2.me/submissions/f8ef7f34-a524-4fce-a0df-03f0eaf92c6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Theorems.Thm_GlobalTheory_SW_HaarAlg_apply_out_mk

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
theorem _root_.solution {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (b : Matrix κ ι K) :
    ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ (q.out - b) =
      ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ q.out := by
  rw [← finsum_comp_equiv (Equiv.subRight (QuotientAddGroup.mk b :
    Matrix κ ι K ⧸ perSub K κ ι R)) (f := fun q => φ q.out)]
  refine finsum_congr fun q => ?_
  rw [← apply_out_mk h (q.out - b), QuotientAddGroup.mk_sub, QuotientAddGroup.out_eq']
  rfl
end GlobalTheory.SW.HaarAlg
