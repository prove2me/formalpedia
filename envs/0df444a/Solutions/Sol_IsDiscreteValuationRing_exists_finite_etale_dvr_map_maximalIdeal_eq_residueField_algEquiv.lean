-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/797458dd-9aa2-51ee-bd56-42ae08845f1b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv

set_option autoImplicit false

universe u v

open Polynomial

namespace UnramifiedExtensionOfDVR

theorem key
    (R : Type u) [CommRing R] [IsLocalRing R] (F : R[X]) :
    ∀ p : R[X], AdjoinRoot.quotEquivQuotMap F (IsLocalRing.maximalIdeal R)
        (Ideal.Quotient.mk _ (AdjoinRoot.mk F p)) = AdjoinRoot.mk (F.map (IsLocalRing.residue R)) (p.map (IsLocalRing.residue R)) :=
  fun p => AdjoinRoot.quotEquivQuotMap_apply_mk F p (IsLocalRing.maximalIdeal R)

end UnramifiedExtensionOfDVR

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k' : Type v) [Field k'] [Algebra (IsLocalRing.ResidueField R) k'] [FiniteDimensional (IsLocalRing.ResidueField R) k']
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) k'] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      Nonempty (k' ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R') := by
  classical

  let pb := Field.powerBasisOfFiniteOfSeparable (IsLocalRing.ResidueField R) k'
  have hint : IsIntegral (IsLocalRing.ResidueField R) pb.gen := IsIntegral.of_finite _ _
  set g : (IsLocalRing.ResidueField R)[X] := minpoly (IsLocalRing.ResidueField R) pb.gen with hg
  have hgm : g.Monic := minpoly.monic hint
  have hgi : Irreducible g := minpoly.irreducible hint
  have hgs : g.Separable := Algebra.IsSeparable.isSeparable (IsLocalRing.ResidueField R) pb.gen
  have hgdeg : 0 < g.degree := minpoly.degree_pos hint
  obtain ⟨F, hFg, hFdeg, hFm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts g).2 (Polynomial.map_surjective _ IsLocalRing.residue_surjective g)) hgm

  have hFdeg0 : F.degree ≠ 0 := by rw [hFdeg]; exact ne_of_gt hgdeg
  haveI : Nontrivial (AdjoinRoot F) := AdjoinRoot.nontrivial F hFdeg0
  haveI : Module.Finite R (AdjoinRoot F) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hFm).basis
  haveI : Module.Free R (AdjoinRoot F) := Module.Free.of_basis (AdjoinRoot.powerBasis' hFm).basis
  haveI : Module.FaithfullyFlat R (AdjoinRoot F) := inferInstance
  haveI hfact : Fact (Irreducible (F.map (IsLocalRing.residue R))) := ⟨by rw [hFg]; exact hgi⟩

  set 𝔪' : Ideal (AdjoinRoot F) := Ideal.map (algebraMap R (AdjoinRoot F)) (IsLocalRing.maximalIdeal R) with h𝔪'
  have h𝔪'of : 𝔪' = Ideal.map (AdjoinRoot.of F) (IsLocalRing.maximalIdeal R) := by
    rw [h𝔪', AdjoinRoot.algebraMap_eq]

  let θ₀ : (AdjoinRoot F ⧸ 𝔪') ≃+* AdjoinRoot (F.map (IsLocalRing.residue R)) :=
    (Ideal.quotEquivOfEq h𝔪'of).trans (AdjoinRoot.quotEquivQuotMap F (IsLocalRing.maximalIdeal R)).toRingEquiv
  have hθ₀ : ∀ p : R[X], θ₀ (Ideal.Quotient.mk 𝔪' (AdjoinRoot.mk F p)) =
      AdjoinRoot.mk (F.map (IsLocalRing.residue R)) (p.map (IsLocalRing.residue R)) := by
    intro p
    show AdjoinRoot.quotEquivQuotMap F (IsLocalRing.maximalIdeal R)
      (Ideal.quotEquivOfEq h𝔪'of (Ideal.Quotient.mk 𝔪' (AdjoinRoot.mk F p))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact UnramifiedExtensionOfDVR.key R F p
  have hfield : IsField (AdjoinRoot F ⧸ 𝔪') :=
    MulEquiv.isField (Field.toIsField (AdjoinRoot (F.map (IsLocalRing.residue R)))) θ₀.toMulEquiv
  have hmax : 𝔪'.IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield

  haveI : Algebra.IsIntegral R (AdjoinRoot F) := Algebra.IsIntegral.of_finite R _
  haveI hloc : IsLocalRing (AdjoinRoot F) := by
    refine IsLocalRing.of_unique_max_ideal ⟨𝔪', hmax, fun M hM => ?_⟩
    haveI := hM
    have hc : (M.comap (algebraMap R (AdjoinRoot F))) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
    have hle : 𝔪' ≤ M := by
      rw [h𝔪', ← hc]; exact Ideal.map_comap_le
    exact (hmax.eq_of_le hM.ne_top hle).symm
  have hmR' : IsLocalRing.maximalIdeal (AdjoinRoot F) = 𝔪' := (IsLocalRing.eq_maximalIdeal hmax).symm
  haveI hlh : IsLocalHom (algebraMap R (AdjoinRoot F)) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R (AdjoinRoot F))).out 0 2).mpr (by rw [← h𝔪', hmR'])

  have hunit : ∀ p : R[X], AdjoinRoot.mk (F.map (IsLocalRing.residue R)) (p.map (IsLocalRing.residue R)) ≠ 0 →
      IsUnit (AdjoinRoot.mk F p) := by
    intro p hp
    by_contra hnu
    have hmem : AdjoinRoot.mk F p ∈ IsLocalRing.maximalIdeal (AdjoinRoot F) :=
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
    rw [hmR'] at hmem
    have h0 : Ideal.Quotient.mk 𝔪' (AdjoinRoot.mk F p) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    apply hp
    rw [← hθ₀ p, h0, map_zero]

  have hderiv : IsUnit (AdjoinRoot.mk F (derivative F)) := by
    apply hunit
    rw [← Polynomial.derivative_map]
    have hfs : (F.map (IsLocalRing.residue R)).Separable := by rw [hFg]; exact hgs
    obtain ⟨a, b, hab⟩ := hfs
    intro h0
    have h1 : AdjoinRoot.mk (F.map (IsLocalRing.residue R))
        (a * F.map (IsLocalRing.residue R) + b * derivative (F.map (IsLocalRing.residue R))) = 1 := by
      rw [hab, map_one]
    rw [map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, h0, mul_zero] at h1
    exact zero_ne_one h1

  have hFi : Irreducible F := hFm.irreducible_of_irreducible_map (IsLocalRing.residue R) F (by rw [hFg]; exact hgi)
  haveI hdom : IsDomain (AdjoinRoot F) := AdjoinRoot.isDomain_of_prime hFi.prime

  haveI : IsNoetherianRing (AdjoinRoot F) := Algebra.FiniteType.isNoetherianRing R (AdjoinRoot F)
  obtain ⟨ϖ, hϖ⟩ := (inferInstance : (IsLocalRing.maximalIdeal R).IsPrincipal)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field R
    rw [hϖ]
    exact Submodule.span_zero_singleton R
  have hgen : IsLocalRing.maximalIdeal (AdjoinRoot F) = Ideal.span {algebraMap R (AdjoinRoot F) ϖ} := by
    rw [hmR', h𝔪', hϖ]
    show Ideal.map (algebraMap R (AdjoinRoot F)) (Ideal.span {ϖ}) = _
    rw [Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (AdjoinRoot F) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hgen, Ideal.span_singleton_eq_bot, AdjoinRoot.algebraMap_eq]
    intro h
    exact hϖ0 (AdjoinRoot.of.injective_of_degree_ne_zero hFdeg0 (by rw [h, map_zero]))
  have hpr : (IsLocalRing.maximalIdeal (AdjoinRoot F)).IsPrincipal := ⟨⟨algebraMap R (AdjoinRoot F) ϖ, hgen⟩⟩
  haveI hdvr : IsDiscreteValuationRing (AdjoinRoot F) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot F) hnf).out 0 4).mpr hpr

  obtain ⟨u, hu⟩ := hderiv.exists_right_inv
  obtain ⟨p₁, rfl⟩ := AdjoinRoot.mk_surjective u
  have hdvd : F ∣ derivative F * p₁ - 1 := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, hu, map_one, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  let P : StandardEtalePair R :=
    ⟨F, hFm, 1, p₁, -q, 0, by rw [pow_zero, mul_neg, ← hq]; ring⟩
  have hP1 : Submonoid.powers (AdjoinRoot.mk P.f P.g) ≤ IsUnit.submonoid (AdjoinRoot F) := by
    refine Submonoid.powers_le.2 ?_
    show IsUnit (AdjoinRoot.mk F 1)
    rw [map_one]; exact isUnit_one
  let e₁ : P.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) := P.equivAwayAdjoinRoot
  let e₂ : AdjoinRoot F ≃ₐ[AdjoinRoot F] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    IsLocalization.atUnits (AdjoinRoot F) (Submonoid.powers (AdjoinRoot.mk P.f P.g)) hP1
  let e : P.Ring ≃ₐ[R] AdjoinRoot F := e₁.trans (e₂.restrictScalars R).symm
  haveI : Algebra.IsStandardEtale R (AdjoinRoot F) := Algebra.IsStandardEtale.of_equiv e
  haveI het : Algebra.Etale R (AdjoinRoot F) := inferInstance

  have hθ : ∀ x : IsLocalRing.ResidueField R,
      ((Ideal.quotEquivOfEq hmR').trans θ₀) (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (AdjoinRoot F)) x) =
        algebraMap (IsLocalRing.ResidueField R) (AdjoinRoot (F.map (IsLocalRing.residue R))) x := by
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.algebraMap_residue, AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq]
    show θ₀ (Ideal.quotEquivOfEq hmR' (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AdjoinRoot F)) (AdjoinRoot.mk F (C r)))) =
      AdjoinRoot.mk (F.map (IsLocalRing.residue R)) (C (IsLocalRing.residue R r))
    rw [Ideal.quotEquivOfEq_mk, hθ₀, Polynomial.map_C]
  let θ : IsLocalRing.ResidueField (AdjoinRoot F) ≃ₐ[IsLocalRing.ResidueField R] AdjoinRoot (F.map (IsLocalRing.residue R)) :=
    AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq hmR').trans θ₀) hθ
  have h₁ : aeval (AdjoinRoot.root (F.map (IsLocalRing.residue R))) (minpoly (IsLocalRing.ResidueField R) pb.gen) = 0 := by
    rw [← hg, ← hFg, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h₂ : aeval pb.gen (F.map (IsLocalRing.residue R)) = 0 := by
    rw [hFg]; exact minpoly.aeval _ _
  let e₃ : AdjoinRoot (F.map (IsLocalRing.residue R)) ≃ₐ[IsLocalRing.ResidueField R] k' := AdjoinRoot.equiv' _ pb h₁ h₂
  exact ⟨AdjoinRoot F, inferInstance, hdom, hdvr, inferInstance, inferInstance, het, inferInstance, hlh,
    by rw [← h𝔪', hmR'], ⟨(θ.trans e₃).symm⟩⟩

end S_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv (solution)
