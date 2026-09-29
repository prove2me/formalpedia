-- Prove2me | solution 1 for IsGaloisGroup.finrank_eq_index_of_isFractionRing_fixedPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3c642c29-429d-5b3c-8d4d-ee1e3545eeef

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsGaloisGroup_finrank_eq_index_of_isFractionRing_fixedPoints

set_option autoImplicit false

open Module

namespace FracDegFixedAux

theorem finrank_eq_index_core
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra C B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (H : Subgroup G) [IsGaloisGroup H C B]
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra C E] [IsFractionRing C E]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra E L] [Algebra K E] [IsScalarTower K E L]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Algebra C L] [IsScalarTower C E L] [IsScalarTower C B L]
    [MulSemiringAction G L] [SMulDistribClass G B L] :
    finrank K E = H.index := by
  haveI : IsGaloisGroup G K L := IsGaloisGroup.to_isFractionRing G A B K L
  haveI : SMulDistribClass H B L :=
    ⟨fun h b l => SMulDistribClass.smul_distrib_smul (h : G) b l⟩
  haveI : IsGaloisGroup H E L := IsGaloisGroup.to_isFractionRing H C B E L
  have hG := IsGaloisGroup.card_eq_finrank G K L
  have hH := IsGaloisGroup.card_eq_finrank H E L
  have htower := Module.finrank_mul_finrank K E L
  have hidx := H.card_mul_index
  have hpos : 0 < Nat.card H := Nat.card_pos
  have key : finrank K E * Nat.card H = H.index * Nat.card H := by
    rw [mul_comm H.index, hidx, hG, ← htower, hH]
  exact Nat.eq_of_mul_eq_mul_right hpos key

end FracDegFixedAux

theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (H : Subgroup G)
    (K E : Type*) [Field K] [Field E] [Algebra A K] [IsFractionRing A K]
    [Algebra (FixedPoints.subalgebra A B H) E] [IsFractionRing (FixedPoints.subalgebra A B H) E]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [IsScalarTower A (FixedPoints.subalgebra A B H) E] :
    Module.finrank K E = H.index := by
  haveI hGB : FaithfulSMul G B := IsGaloisGroup.faithful A
  haveI : IsGaloisGroup H (FixedPoints.subalgebra A B H) B :=
    { faithful := inferInstance
      commutes := ⟨fun h c b => by
        rw [Algebra.smul_def, Algebra.smul_def, smul_mul',
          show h • algebraMap (FixedPoints.subalgebra A B H) B c
            = algebraMap (FixedPoints.subalgebra A B H) B c from c.2 h]⟩
      isInvariant := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩ }
  have hAL : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp
      (FaithfulSMul.algebraMap_injective A B)
  have hCL : Function.Injective
      (algebraMap (FixedPoints.subalgebra A B H) (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq (FixedPoints.subalgebra A B H) B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp Subtype.val_injective
  letI : Algebra K (FractionRing B) := (IsFractionRing.lift hAL).toAlgebra
  haveI : IsScalarTower A K (FractionRing B) :=
    IsScalarTower.of_algebraMap_eq fun a => (IsFractionRing.lift_algebraMap hAL a).symm
  letI : Algebra E (FractionRing B) := (IsFractionRing.lift hCL).toAlgebra
  haveI : IsScalarTower (FixedPoints.subalgebra A B H) E (FractionRing B) :=
    IsScalarTower.of_algebraMap_eq fun c => (IsFractionRing.lift_algebraMap hCL c).symm
  haveI : IsScalarTower K E (FractionRing B) := by
    refine IsScalarTower.of_algebraMap_eq' (IsFractionRing.ringHom_ext (A := A) fun a => ?_)
    change IsFractionRing.lift hAL (algebraMap A K a)
      = IsFractionRing.lift hCL (algebraMap K E (algebraMap A K a))
    rw [IsFractionRing.lift_algebraMap, ← IsScalarTower.algebraMap_apply A K E,
      IsScalarTower.algebraMap_apply A (FixedPoints.subalgebra A B H) E,
      IsFractionRing.lift_algebraMap, IsScalarTower.algebraMap_apply A B (FractionRing B),
      IsScalarTower.algebraMap_apply (FixedPoints.subalgebra A B H) B (FractionRing B),
      ← IsScalarTower.algebraMap_apply A (FixedPoints.subalgebra A B H) B]
  letI : MulSemiringAction G (FractionRing B) :=
    IsFractionRing.mulSemiringAction G B (FractionRing B)
  haveI : SMulDistribClass G B (FractionRing B) :=
    IsFractionRing.smulDistribClass G B (FractionRing B)
  exact FracDegFixedAux.finrank_eq_index_core A B (FixedPoints.subalgebra A B H) G H K E
    (FractionRing B)

#print axioms solution

end S_IsGaloisGroup_finrank_eq_index_of_isFractionRing_fixedPoints
end P2MW
export P2MW.S_IsGaloisGroup_finrank_eq_index_of_isFractionRing_fixedPoints (solution)
