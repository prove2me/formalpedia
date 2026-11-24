-- Prove2me | solution 1 for GlobalTheory.ClassFin.gramLB_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:14.055024+00:00
-- url     : https://prove2.me/submissions/2e051e77-e99a-4904-a57e-52be4f9fca55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {g : Matrix n n ℝ}
    (hg : g.det ≠ 0) : (gᵀ * g).PosDef := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact PosDef.conjTranspose_mul_self g
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (Ne.isUnit hg)))
end GlobalTheory.ClassFin
