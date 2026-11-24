-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.length_localized_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:52:13.076908+00:00
-- url     : https://prove2.me/submissions/c1a905b5-e96e-4f75-92a6-5d3daff4d59e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.IntersectionSymm
namespace GlobalTheory.IntersectionSymm
theorem _root_.solution {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) (a : A) (ha : a ≠ 0) :
    Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span {algebraMap A (Localization.AtPrime p) a}) ≠ ⊤ := by
  haveI : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p, hp]
    rfl
  rw [Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  apply mem_nonZeroDivisors_of_ne_zero
  exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _
    (Ideal.primeCompl_le_nonZeroDivisors p) (mem_nonZeroDivisors_of_ne_zero ha)
end GlobalTheory.IntersectionSymm
