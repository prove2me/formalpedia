-- Prove2me | solution 1 for HatAffineOffsets.typeII_offsetCoverable_iff_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:23:23.46126+00:00
-- url     : https://prove2.me/submissions/097f6d4c-fddf-4358-aa11-50e46cfabb3a

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_typeII_offsetCoverable_iff_cross
import Theorems.Thm_HatAffineOffsets_typeII_cross_iff_good

set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (u v : Fin m)
    (alpha c b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (huv : u ≠ v)
    (halpha : forall i, alpha i ≠ 0)
    (hc : forall i, c i ≠ 0)
    (hsurj : forall z : K, z ≠ 0 -> exists i, c i = z)
    (hrealizeII : forall y i,
      F y i = alpha i * (y u - c i * y v) + b i)
    (x : Fin (Fintype.card K - 1) -> K) :
    OffsetCoverable F x ↔ TypeIIGood c (typeIID alpha b x) := by
  rw [typeII_offsetCoverable_iff_cross hm hq u v alpha c b F huv halpha
    hrealizeII x]
  exact typeII_cross_iff_good hq c (typeIID alpha b x) hc hsurj
end HatAffineOffsets
