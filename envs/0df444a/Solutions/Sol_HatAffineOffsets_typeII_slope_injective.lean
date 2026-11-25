-- Prove2me | solution 1 for HatAffineOffsets.typeII_slope_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:18:52.282121+00:00
-- url     : https://prove2.me/submissions/d678daea-48c7-4ca1-8df9-9aa4d2e18d46

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_nonzero_subtype_card

set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K]
    (hq : 4 <= Fintype.card K)
    (c : Fin (Fintype.card K - 1) -> K)
    (hc : forall i, c i ≠ 0)
    (hsurj : forall z : K, z ≠ 0 -> exists i, c i = z) :
    Function.Injective c := by
  classical
  let cNZ : Fin (Fintype.card K - 1) -> {z : K // z ≠ 0} :=
    fun i => ⟨c i, hc i⟩
  have hsurjNZ : Function.Surjective cNZ := by
    intro z
    obtain ⟨i, hi⟩ := hsurj z.1 z.2
    refine ⟨i, ?_⟩
    exact Subtype.ext hi
  have hcard :
      Fintype.card (Fin (Fintype.card K - 1)) =
        Fintype.card {z : K // z ≠ 0} := by
    rw [Fintype.card_fin, nonzero_subtype_card]
  have hbij : Function.Bijective cNZ :=
    (Fintype.bijective_iff_surjective_and_card cNZ).mpr ⟨hsurjNZ, hcard⟩
  intro i j hij
  apply hbij.1
  exact Subtype.ext hij
end HatAffineOffsets
