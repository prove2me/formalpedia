-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.dim_quotient_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:47.553798+00:00
-- url     : https://prove2.me/submissions/db35ec27-92af-4822-a36d-66ef3f3b1a78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
import Theorems.Thm_GlobalTheory_IntersectionSymm_height_add_dim_quotient_le
import Theorems.Thm_GlobalTheory_IntersectionSymm_arith
import Theorems.Thm_GlobalTheory_IntersectionSymm_not_dim_quotient_le_zero

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
theorem _root_.solution {A : Type} [CommRing A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    ringKrullDim (A ⧸ p) = 1 := by
  have h1 := height_add_dim_quotient_le p
  rw [hA] at h1
  have hne : ¬ p.IsMaximal := by
    intro hm
    have := maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [← IsLocalRing.eq_maximalIdeal hm, hp, hA] at this
    exact absurd this (by decide)
  exact (arith _ _ h1 (not_dim_quotient_le_zero p hne)).2 hp
end GlobalTheory.IntersectionSymm
