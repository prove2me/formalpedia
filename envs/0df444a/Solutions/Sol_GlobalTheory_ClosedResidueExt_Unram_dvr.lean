-- Prove2me | solution 1 for GlobalTheory.ClosedResidueExt.Unram.dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:33.037243+00:00
-- url     : https://prove2.me/submissions/4a9e0515-da67-4ea1-af8a-7739c2e7b198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
import Theorems.Thm_GlobalTheory_ClosedResidueExt_Unram_factor
import Theorems.Thm_GlobalTheory_ClosedResidueExt_Unram_irreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
namespace GlobalTheory.ClosedResidueExt
namespace Unram
theorem _root_.solution {π : W} {R : Subalgebra W Ω} (h : Unram π R)
    (h0 : algebraMap W Ω π ≠ 0) : IsDiscreteValuationRing R :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, h.irreducible h0, fun {x} hx => h.factor x hx⟩
end Unram
end GlobalTheory.ClosedResidueExt
