-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:55:35.063981+00:00
-- url     : https://prove2.me/submissions/79e7acfa-5975-435c-afd1-ac238a2ae062

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian GroundTheory.Arith.Abelian.Jacobian
open Algebra Cardinal
universe u
variable {A : Type u} [CommRing A] [IsDomain A]
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution (p : Ideal A) (hp : p ≠ ⊥) :
    ringKrullDim (A ⧸ p) + 1 ≤ ringKrullDim A := by
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
end GroundTheory.Arith.Abelian.Jacobian
