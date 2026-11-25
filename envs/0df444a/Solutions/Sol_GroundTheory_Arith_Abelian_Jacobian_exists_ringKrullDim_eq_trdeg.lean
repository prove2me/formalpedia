-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:02.583476+00:00
-- url     : https://prove2.me/submissions/d2a0795e-9884-47cc-adf5-db4130d14b6f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_of_normalization
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_trdeg_eq_of_normalization

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
theorem _root_.solution [IsDomain A] :
    ∃ n : ℕ, ringKrullDim A = n ∧ trdeg k A = n := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  exact ⟨s, ringKrullDim_eq_of_normalization k g hinj hint,
    trdeg_eq_of_normalization k g hinj hint⟩
end GroundTheory.Arith.Abelian.Jacobian
