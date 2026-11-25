-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:11.60032+00:00
-- url     : https://prove2.me/submissions/0f58b937-7be1-477b-8ab4-197ba764fee3

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_coheight_eq_ringKrullDim_quotient
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_le_height_add_ringKrullDim_quotient

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
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]
include k
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution (p : Ideal A) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) = ringKrullDim A := by
  refine le_antisymm ?_ ?_
  · rw [← coheight_eq_ringKrullDim_quotient (⟨p, inferInstance⟩ : PrimeSpectrum A),
      show p.height = (⟨p, inferInstance⟩ : PrimeSpectrum A).asIdeal.height from rfl,
      PrimeSpectrum.height_eq_orderHeight, ringKrullDim,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact_mod_cast le_iSup (fun a : PrimeSpectrum A => Order.height a + Order.coheight a) _
  · obtain ⟨n, hn, -⟩ := exists_ringKrullDim_eq_trdeg (k := k) (A := A)
    exact ringKrullDim_le_height_add_ringKrullDim_quotient k n A hn p
end GroundTheory.Arith.Abelian.Jacobian
