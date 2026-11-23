-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.not_dim_quotient_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:34.003932+00:00
-- url     : https://prove2.me/submissions/43fd8ef1-2d09-450f-a476-1c7bebb9facc

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
theorem _root_.solution {A : Type} [CommRing A] (p : Ideal A) [p.IsPrime]
    (hne : ¬ p.IsMaximal) : ¬ ringKrullDim (A ⧸ p) ≤ 0 := by
  intro h
  haveI : Ring.KrullDimLE 0 (A ⧸ p) := Ring.krullDimLE_iff.2 (by exact_mod_cast h)
  exact hne (Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain)
end GlobalTheory.IntersectionSymm
