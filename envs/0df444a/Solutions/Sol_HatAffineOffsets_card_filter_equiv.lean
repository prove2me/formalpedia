-- Prove2me | solution 1 for HatAffineOffsets.card_filter_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:22:05.280849+00:00
-- url     : https://prove2.me/submissions/b1c4ad4d-676d-4aaf-ac6a-24d49cd1fd13

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI

set_option autoImplicit true
open HatAffineOffsets
universe u v w
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_8d02a9c2cf_10
namespace HatAffineOffsets
theorem _root_.solution
    {X : Type v} {Y : Type w} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : Y -> Prop) :
    (Finset.univ.filter (fun x => p (e x))).card =
      (Finset.univ.filter p).card := by
  classical
  calc
    (Finset.univ.filter (fun x => p (e x))).card =
        Fintype.card {x : X // p (e x)} :=
      (Fintype.card_subtype (fun x : X => p (e x))).symm
    _ = Fintype.card {y : Y // p y} :=
      Fintype.card_congr e.subtypeEquivOfSubtype
    _ = (Finset.univ.filter p).card :=
      Fintype.card_subtype p
end HatAffineOffsets
