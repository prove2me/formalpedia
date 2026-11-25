-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:59.800785+00:00
-- url     : https://prove2.me/submissions/180085ef-2bf1-4ee3-8435-1b083f4b1305

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg

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
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A]
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution [IsDomain A] : ringKrullDim A = (trdeg k A).toENat := by
  obtain ⟨n, h1, h2⟩ := exists_ringKrullDim_eq_trdeg (k := k) (A := A)
  rw [h1, h2]
  simp
end GroundTheory.Arith.Abelian.Jacobian
