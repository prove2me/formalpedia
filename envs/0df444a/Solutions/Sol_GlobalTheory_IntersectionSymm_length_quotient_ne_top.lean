-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.length_quotient_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:51:32.867883+00:00
-- url     : https://prove2.me/submissions/d30a77f6-88c8-48af-a221-6424b03c7145

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
theorem _root_.solution {A : Type} [CommRing A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (hd : ringKrullDim (A ⧸ p) = 1) (b : A) (hb : b ∉ p) :
    Module.length (A ⧸ p) ((A ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p b}) ≠ ⊤ := by
  haveI : Ring.KrullDimLE 1 (A ⧸ p) := by
    rw [Ring.krullDimLE_iff, hd]
    rfl
  rw [Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  apply mem_nonZeroDivisors_of_ne_zero
  rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
end GlobalTheory.IntersectionSymm
