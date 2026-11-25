-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:30.286409+00:00
-- url     : https://prove2.me/submissions/49e3c5dc-518c-440f-9ddd-1411f73ed860

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_of_normalization

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
include k
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution : ringKrullDim A < ⊤ := by
  nontriviality A
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  rw [ringKrullDim_eq_of_normalization k g hinj hint]
  exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top s)
end GroundTheory.Arith.Abelian.Jacobian
