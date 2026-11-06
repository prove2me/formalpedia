-- Prove2me | solution 1 for Ideal.finrank_eq_inertiaDegIn_of_quotient_equivs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:03:48.547209+00:00
-- url     : https://prove2.me/submissions/6ec3e1ba-0d82-4cca-af07-53be5dcf4596

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneQuotientResidue
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ResidueFinrankInertia

set_option autoImplicit false
open Ideal
noncomputable section
namespace Ideal
theorem _root_.solution
    {k O C S G : Type*} [Field k] [Finite k]
    [CommRing O] [IsDedekindDomain O] [CommRing C] [IsDedekindDomain C]
    [Algebra O C] [Module.Finite O C]
    [Field S] [Algebra k S] [FiniteDimensional k S]
    [Group G] [Finite G] [MulSemiringAction G C] [IsGaloisGroup G O C]
    (p : Ideal O) [p.IsMaximal] (P : p.primesOver C) [P.1.IsMaximal]
    (baseEquiv : k ≃+* (O ⧸ p))
    (upperEquiv : (C ⧸ P.1) ≃+* S) :
    Module.finrank k S = p.inertiaDegIn C := by
  let R : Ideal C := P.1
  letI : p.IsPrime := (inferInstance : p.IsMaximal).isPrime
  letI : R.IsPrime := P.2.1
  letI : R.LiesOver p := P.2.2
  letI : R.IsMaximal := by
    change P.1.IsMaximal
    infer_instance
  letI : _root_.Field (O ⧸ p) := Ideal.Quotient.field p
  letI : _root_.Field (C ⧸ R) := Ideal.Quotient.field R
  let quotientAlgebra : Algebra (O ⧸ p) (C ⧸ R) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def R p).le
  letI : Algebra (O ⧸ p) (C ⧸ R) := quotientAlgebra
  letI : SMul (O ⧸ p) (C ⧸ R) := quotientAlgebra.toSMul
  letI : Module (O ⧸ p) (C ⧸ R) :=
    @Algebra.toModule (O ⧸ p) (C ⧸ R) _ _ quotientAlgebra
  letI : Module.Free (O ⧸ p) (C ⧸ R) :=
    Module.Free.of_divisionRing (O ⧸ p) (C ⧸ R)
  letI : FiniteDimensional (O ⧸ p) (C ⧸ R) := by
    infer_instance
  let baseAlgebra : Algebra k (O ⧸ p) :=
    baseEquiv.toRingHom.toAlgebra
  letI : Algebra k (O ⧸ p) := baseAlgebra
  let upperAlgebra : Algebra k (C ⧸ R) :=
    ((algebraMap (O ⧸ p) (C ⧸ R)).comp
      (algebraMap k (O ⧸ p))).toAlgebra
  letI : Algebra k (C ⧸ R) := upperAlgebra
  letI : IsScalarTower k (O ⧸ p) (C ⧸ R) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional k (O ⧸ p) := by
    exact FiniteDimensional.of_surjective
      (Algebra.linearMap k (O ⧸ p)) baseEquiv.surjective
  letI : FiniteDimensional k (C ⧸ R) :=
    FiniteDimensional.trans k (O ⧸ p) (C ⧸ R)
  have hquotient : Module.finrank k S = Module.finrank k (C ⧸ R) := by
    apply Nat.pow_right_injective (a := Nat.card k) (by
      letI : Fintype k := Fintype.ofFinite k
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card)
    change Nat.card k ^ Module.finrank k S =
      Nat.card k ^ Module.finrank k (C ⧸ R)
    rw [← Module.natCard_eq_pow_finrank (K := k) (V := S),
      ← Module.natCard_eq_pow_finrank (K := k) (V := C ⧸ R)]
    exact Nat.card_congr upperEquiv.toEquiv.symm
  calc
    Module.finrank k S = Module.finrank k (C ⧸ R) := hquotient
    _ = Module.finrank k (O ⧸ p) *
        Module.finrank (O ⧸ p) (C ⧸ R) :=
      (Module.finrank_mul_finrank k (O ⧸ p) (C ⧸ R)).symm
    _ = 1 * p.inertiaDeg' R := by
      congr 1
      · apply Module.finrank_of_bijective_algebraMap
        exact baseEquiv.bijective
      · rw [← Ideal.inertiaDeg_algebraMap]
    _ = p.inertiaDeg' R := Nat.one_mul _
    _ = p.inertiaDegIn C := by
      rw [Ideal.inertiaDeg'_eq_inertiaDeg]
      exact (Ideal.inertiaDegIn_eq_inertiaDeg p R G).symm
end Ideal
