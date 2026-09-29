-- Prove2me | solution 1 for IsDedekindDomain.etale_quotient_map_span_of_forall_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/12ffec7e-dbc9-5b0d-858f-51ce214cfd3e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_etale_quotient_map_span_of_forall_isUnramifiedAt

set_option autoImplicit false

open Polynomial Algebra

universe u

namespace HpoolG2

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k[X] B]

theorem formallyUnramified_quotient_of_forall {R : Type*} [CommRing R] [Algebra R B] (I : Ideal B)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], I ≤ P → Algebra.IsUnramifiedAt R P) :
    Algebra.FormallyUnramified R (B ⧸ I) := by
  rw [Algebra.formallyUnramified_iff_forall]
  intro Q

  let P : Ideal B := Q.1.comap (Ideal.Quotient.mk I)
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hIP : I ≤ P := fun x hx => by
    show Ideal.Quotient.mk I x ∈ Q.1
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact Q.1.zero_mem
  haveI : Algebra.IsUnramifiedAt R P := hunr P hIP

  let φ : Localization.AtPrime P →+* Localization.AtPrime Q.1 :=
    Localization.localRingHom P Q.1 (Ideal.Quotient.mk I) rfl
  have hφ : Function.Surjective φ :=
    RingHom.surjective_localRingHom_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q.1
  have hφalg : ∀ r : R, φ (algebraMap R _ r) = algebraMap R _ r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime P), Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply R (B ⧸ I) (Localization.AtPrime Q.1)]
    rfl
  let φa : Localization.AtPrime P →ₐ[R] Localization.AtPrime Q.1 :=
    { φ with commutes' := hφalg }
  exact Algebra.FormallyUnramified.of_surjective φa hφ

end HpoolG2

open HpoolG2 in
theorem solution
    {k : Type u} [Field k] (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]) (hirr : Irreducible h) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ → Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) := by
  classical
  set I : Ideal B := Ideal.map (algebraMap k[X] B) (Ideal.span {h}) with hI
  have h0 : h ≠ 0 := hirr.ne_zero
  have hinj : Function.Injective (algebraMap k[X] B) := FaithfulSMul.algebraMap_injective k[X] B

  have hU : Algebra.FormallyUnramified k[X] (B ⧸ I) := by
    refine formallyUnramified_quotient_of_forall I (fun P _ hIP => ?_)
    have hhP : algebraMap k[X] B h ∈ P := hIP (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self h))
    have hP0 : P ≠ ⊥ := fun hP => by
      rw [hP, Ideal.mem_bot, map_eq_zero_iff _ hinj] at hhP; exact h0 hhP
    refine hunr P hP0 ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; exact hhP

  set 𝔪 : Ideal k[X] := I.comap (algebraMap k[X] B) with h𝔪
  have hle : Ideal.span {h} ≤ 𝔪 := Ideal.le_comap_map.trans (le_of_eq rfl)
  haveI hmax : (Ideal.span {h}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr

  haveI : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  haveI : Algebra.FiniteType k (B ⧸ I) := Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom k B (B ⧸ I)) Ideal.Quotient.mk_surjective
  haveI : Algebra.FinitePresentation k (B ⧸ I) := (Algebra.FinitePresentation.of_finiteType (R := k) (A := B ⧸ I)).mp inferInstance
  by_cases hItop : I = ⊤
  ·
    haveI : Subsingleton (B ⧸ I) := Ideal.Quotient.subsingleton_iff.2 hItop
    haveI : Algebra.FormallyUnramified k (B ⧸ I) :=
      Algebra.FormallyUnramified.of_surjective (Algebra.ofId k (B ⧸ I)) (fun b => ⟨0, Subsingleton.elim _ _⟩)
    exact ⟨Algebra.FormallyEtale.of_formallyUnramified_of_field k (B ⧸ I), inferInstance⟩
  · have h𝔪ne : 𝔪 ≠ ⊤ := by
      intro htop
      apply hItop
      rw [Ideal.eq_top_iff_one]
      have : (1 : k[X]) ∈ 𝔪 := by rw [htop]; trivial
      simpa using (Ideal.mem_comap.1 this)
    have h𝔪eq : 𝔪 = Ideal.span {h} := (hmax.eq_of_le h𝔪ne hle).symm
    haveI : 𝔪.IsMaximal := h𝔪eq ▸ hmax
    letI : Field (k[X] ⧸ 𝔪) := Ideal.Quotient.field 𝔪

    haveI : Fact (Irreducible h) := ⟨hirr⟩
    have hsepK : Algebra.IsSeparable k (k[X] ⧸ 𝔪) := by
      have e : (k[X] ⧸ 𝔪) ≃ₐ[k] AdjoinRoot h := Ideal.quotientEquivAlgOfEq k h𝔪eq
      haveI : Algebra.IsSeparable k (AdjoinRoot h) := by
        have hroot : IsSeparable k (AdjoinRoot.root h) := by
          refine hsep.of_dvd (minpoly.dvd k (AdjoinRoot.root h) ?_)
          rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
        have htop : IntermediateField.adjoin k ({AdjoinRoot.root h} : Set (AdjoinRoot h)) = ⊤ := by
          rw [← IntermediateField.toSubalgebra_injective.eq_iff, IntermediateField.top_toSubalgebra]
          exact top_le_iff.mp ((AdjoinRoot.adjoinRoot_eq_top (f := h)).symm.le.trans (IntermediateField.algebra_adjoin_le_adjoin k _))
        haveI : Algebra.IsSeparable k (IntermediateField.adjoin k ({AdjoinRoot.root h} : Set (AdjoinRoot h))) :=
          (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k (AdjoinRoot h)).2 hroot
        exact AlgEquiv.Algebra.isSeparable ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
      exact AlgEquiv.Algebra.isSeparable e.symm
    haveI : Algebra.FormallyUnramified k (k[X] ⧸ 𝔪) := by
      haveI := hsepK; exact Algebra.FormallyUnramified.of_isSeparable k (k[X] ⧸ 𝔪)

    haveI : Algebra.FormallyUnramified (k[X] ⧸ 𝔪) (B ⧸ I) :=
      Algebra.FormallyUnramified.of_restrictScalars k[X] (k[X] ⧸ 𝔪) (B ⧸ I)
    haveI : IsScalarTower k (k[X] ⧸ 𝔪) (B ⧸ I) := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply k k[X] (B ⧸ I), IsScalarTower.algebraMap_apply k k[X] (k[X] ⧸ 𝔪),
        IsScalarTower.algebraMap_apply k[X] (k[X] ⧸ 𝔪) (B ⧸ I)])
    haveI : Algebra.FormallyUnramified k (B ⧸ I) := Algebra.FormallyUnramified.comp k (k[X] ⧸ 𝔪) (B ⧸ I)
    exact ⟨Algebra.FormallyEtale.of_formallyUnramified_of_field k (B ⧸ I), inferInstance⟩

end S_IsDedekindDomain_etale_quotient_map_span_of_forall_isUnramifiedAt
end P2MW
export P2MW.S_IsDedekindDomain_etale_quotient_map_span_of_forall_isUnramifiedAt (solution)
