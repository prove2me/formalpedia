-- Prove2me | solution 1 for HatAffineOffsets.genericTypeII_coverable_offset_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:27:17.773567+00:00
-- url     : https://prove2.me/submissions/7bf3b5c5-c2d9-48c9-aa2a-c75390cfd229

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_typeII_coverable_offset_count
import Theorems.Thm_HatAffineOffsets_sum_typeII_row

set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (A : Fin (Fintype.card K - 1) -> Fin m -> K)
    (lambda : Fin m -> K)
    (b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (hII : HatAffineFactorAlignment.GenericTypeII A lambda)
    (hrealize : HatAffineConstantRows.AffineRealizes A b F) :
    (Finset.univ.filter
      (fun x : Fin (Fintype.card K - 1) -> K =>
        OffsetCoverable F x)).card =
      (Fintype.card K) ^ 2 := by
  classical
  obtain ⟨u, v, alpha, c, mu, huv, hmu, halpha, hc, hsurj, hA,
    hlambda⟩ := hII
  apply typeII_coverable_offset_count hm hq u v alpha c b F huv halpha hc hsurj
  intro y i
  rw [hrealize y i, hA i]
  rw [sum_typeII_row u v huv (alpha i) (c i) y]
end HatAffineOffsets
