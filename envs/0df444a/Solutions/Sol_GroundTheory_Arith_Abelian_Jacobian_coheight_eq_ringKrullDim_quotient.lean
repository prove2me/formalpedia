-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.coheight_eq_ringKrullDim_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:20:39.75886+00:00
-- url     : https://prove2.me/submissions/1cfe88ff-04a5-429d-9725-f8ca88a34704

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
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]
omit [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution (p : PrimeSpectrum A) :
    (Order.coheight p : WithBot ℕ∞) = ringKrullDim (A ⧸ p.asIdeal) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  refine Order.krullDim_eq_of_orderIso (OrderIso.setCongr _ _ ?_)
  ext q
  simp [PrimeSpectrum.mem_zeroLocus, ← PrimeSpectrum.asIdeal_le_asIdeal]
end GroundTheory.Arith.Abelian.Jacobian
