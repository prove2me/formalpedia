-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_finite_etale_isAdicComplete_residueField_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ccc21345-fa27-55b7-8a78-c94b62f52092

import Mathlib
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_finite_etale_isAdicComplete_residueField_algHom

set_option autoImplicit false

universe u w

open Polynomial IsLocalRing

namespace S17B2P

theorem charZero_of_irreducible_natCast
    {R : Type u} [CommRing R] [IsDomain R] {p : ℕ} (hunif : Irreducible (p : R)) : CharZero R := by
  classical
  obtain ⟨ℓ, hℓ⟩ := CharP.exists R
  haveI := hℓ
  rcases CharP.char_is_prime_or_zero R ℓ with hprime | hzero
  · exfalso
    by_cases hdvd : ℓ ∣ p
    · have h0 : ((p : ℕ) : R) = 0 := (CharP.cast_eq_zero_iff R ℓ p).mpr hdvd
      rw [h0] at hunif
      exact not_irreducible_zero hunif
    · haveI : Fact ℓ.Prime := ⟨hprime⟩
      have hne : ((p : ℕ) : ZMod ℓ) ≠ 0 := by
        intro h
        rw [ZMod.natCast_eq_zero_iff] at h
        exact hdvd h
      have hu : IsUnit ((p : ℕ) : ZMod ℓ) := Ne.isUnit hne
      have hu' := hu.map (ZMod.castHom (dvd_refl ℓ) R)
      rw [map_natCast] at hu'
      exact hunif.not_isUnit hu'
  · subst hzero
    exact CharP.charP_to_charZero R

section AdjoinRoot

variable {R : Type u} [CommRing R] [IsLocalRing R] (P : R[X])

noncomputable def m0 : Ideal (AdjoinRoot P) := (maximalIdeal R).map (AdjoinRoot.of P)

noncomputable def quotEquiv :
    AdjoinRoot P ⧸ m0 P ≃+* AdjoinRoot (P.map (residue R)) :=
  (AdjoinRoot.quotEquivQuotMap P (maximalIdeal R)).toRingEquiv

theorem quotEquiv_mk (g : R[X]) :
    quotEquiv P (Ideal.Quotient.mk (m0 P) (AdjoinRoot.mk P g)) =
      AdjoinRoot.mk (P.map (residue R)) (g.map (residue R)) :=
  AdjoinRoot.quotEquivQuotMap_apply_mk P g (maximalIdeal R)

variable {P}

theorem m0_isMaximal (hirr : Irreducible (P.map (residue R))) : (m0 P).IsMaximal := by
  haveI := Fact.mk hirr
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Field.toIsField (AdjoinRoot (P.map (residue R))))
    (quotEquiv P).toMulEquiv

theorem nontrivial (hirr : Irreducible (P.map (residue R))) :
    Nontrivial (AdjoinRoot P) :=
  nontrivial_of_ne 0 1 fun h => (m0_isMaximal hirr).ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ (m0 P).zero_mem))

theorem isLocalRing (hP : P.Monic) (hirr : Irreducible (P.map (residue R))) :
    IsLocalRing (AdjoinRoot P) := by
  haveI : Module.Finite R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hP).finite
  haveI : Algebra.IsIntegral R (AdjoinRoot P) := Algebra.IsIntegral.of_finite R _
  refine IsLocalRing.of_unique_max_ideal ⟨m0 P, m0_isMaximal hirr, fun M hM => ?_⟩
  haveI := hM
  have hc : (M.comap (algebraMap R (AdjoinRoot P))) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  have hle : m0 P ≤ M := by
    rw [m0, ← AdjoinRoot.algebraMap_eq, ← hc]
    exact Ideal.map_comap_le
  exact ((m0_isMaximal hirr).eq_of_le hM.ne_top hle).symm

theorem maximalIdeal_eq (hP : P.Monic) (hirr : Irreducible (P.map (residue R))) :
    letI := isLocalRing hP hirr
    maximalIdeal (AdjoinRoot P) = m0 P :=
  letI := isLocalRing hP hirr
  (IsLocalRing.eq_maximalIdeal (m0_isMaximal hirr)).symm

theorem isLocalHom (hP : P.Monic) (hirr : Irreducible (P.map (residue R))) :
    IsLocalHom (algebraMap R (AdjoinRoot P)) := by
  letI := isLocalRing hP hirr
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : algebraMap R (AdjoinRoot P) a ∈ maximalIdeal (AdjoinRoot P) := by
    rw [maximalIdeal_eq hP hirr, m0, ← AdjoinRoot.algebraMap_eq]
    exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hna)
  exact (mem_maximalIdeal _).mp hmem ha

theorem etale (hP : P.Monic) (hirr : Irreducible (P.map (residue R)))
    (hsep : (P.map (residue R)).Separable) : Algebra.Etale R (AdjoinRoot P) := by
  letI := isLocalRing hP hirr
  haveI := nontrivial hirr

  obtain ⟨a, b, hab⟩ := hsep
  obtain ⟨b', hb'⟩ := Polynomial.map_surjective (residue R) Ideal.Quotient.mk_surjective b
  haveI := Fact.mk hirr

  have hg1 : quotEquiv P (Ideal.Quotient.mk (m0 P) (AdjoinRoot.mk P (derivative P * b'))) = 1 := by
    rw [quotEquiv_mk, Polynomial.map_mul, ← Polynomial.derivative_map, hb',
      ← map_one (AdjoinRoot.mk (P.map (residue R))), eq_comm, ← sub_eq_zero,
      ← map_sub, AdjoinRoot.mk_eq_zero]
    exact ⟨a, by linear_combination -hab⟩
  have hgu : IsUnit (AdjoinRoot.mk P (derivative P * b')) := by
    by_contra hnu
    have hmem : AdjoinRoot.mk P (derivative P * b') ∈ maximalIdeal (AdjoinRoot P) :=
      (mem_maximalIdeal _).mpr hnu
    rw [maximalIdeal_eq hP hirr] at hmem
    have h0 : Ideal.Quotient.mk (m0 P) (AdjoinRoot.mk P (derivative P * b')) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [h0, map_zero] at hg1
    exact zero_ne_one hg1

  let Q : StandardEtalePair R :=
    { f := P, monic_f := hP, g := derivative P * b', cond := ⟨b', 0, 1, by ring⟩ }
  let e₁ : Q.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk P (derivative P * b')) := Q.equivAwayAdjoinRoot
  let e₂ : AdjoinRoot P ≃ₐ[AdjoinRoot P] Localization.Away (AdjoinRoot.mk P (derivative P * b')) :=
    IsLocalization.atUnit (R := AdjoinRoot P) (S := Localization.Away (AdjoinRoot.mk P (derivative P * b'))) _ hgu
  exact Algebra.Etale.of_equiv (e₁.trans (e₂.restrictScalars R).symm)

noncomputable def residueEquiv (hP : P.Monic) (hirr : Irreducible (P.map (residue R))) :
    letI := isLocalRing hP hirr
    ResidueField (AdjoinRoot P) ≃+* AdjoinRoot (P.map (residue R)) :=
  letI := isLocalRing hP hirr
  (Ideal.quotEquivOfEq (maximalIdeal_eq hP hirr)).trans (quotEquiv P)

theorem residueEquiv_residue_mk (hP : P.Monic) (hirr : Irreducible (P.map (residue R))) (g : R[X]) :
    letI := isLocalRing hP hirr
    residueEquiv hP hirr (residue (AdjoinRoot P) (AdjoinRoot.mk P g))
      = AdjoinRoot.mk (P.map (residue R)) (g.map (residue R)) := by
  letI := isLocalRing hP hirr
  show quotEquiv P (Ideal.quotEquivOfEq (maximalIdeal_eq hP hirr) (Ideal.Quotient.mk _ (AdjoinRoot.mk P g))) = _
  rw [Ideal.quotEquivOfEq_mk]
  exact quotEquiv_mk P g

theorem isDomain [IsDomain R] [UniqueFactorizationMonoid R] (hP : P.Monic)
    (hirr : Irreducible (P.map (residue R))) : IsDomain (AdjoinRoot P) :=
  AdjoinRoot.isDomain_of_prime (hP.irreducible_of_irreducible_map (residue R) P hirr).prime

end AdjoinRoot

end S17B2P

open S17B2P in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (p : ℕ) (hunif : Irreducible (p : R))
    (k₀ : Type w) [Field k₀] [Algebra (IsLocalRing.ResidueField R) k₀]
    [FiniteDimensional (IsLocalRing.ResidueField R) k₀] [Algebra.IsSeparable (IsLocalRing.ResidueField R) k₀] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : CharZero R')
      (_ : Algebra R R') (_ : Module.Finite R R') (_ : Module.Free R R') (_ : Algebra.Etale R R')
      (hloc : IsLocalHom (algebraMap R R')),
      IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧ Irreducible (p : R') ∧
      ∃ e : k₀ →+* IsLocalRing.ResidueField R',
        e.comp (algebraMap (IsLocalRing.ResidueField R) k₀)
          = @IsLocalRing.ResidueField.map R R' _ _ _ _ (algebraMap R R') hloc := by
  classical
  haveI : CharZero R := S17B2P.charZero_of_irreducible_natCast hunif
  have hpmem : (p : R) ∈ maximalIdeal R := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hunif.not_isUnit)

  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (ResidueField R) k₀
  have hθi : IsIntegral (ResidueField R) θ := .of_finite (ResidueField R) θ
  have hQm : (minpoly (ResidueField R) θ).Monic := minpoly.monic hθi
  have hQirr : Irreducible (minpoly (ResidueField R) θ) := minpoly.irreducible hθi
  have hQsep : (minpoly (ResidueField R) θ).Separable := Algebra.IsSeparable.isSeparable (ResidueField R) θ
  let eQ : AdjoinRoot (minpoly (ResidueField R) θ) ≃ₐ[ResidueField R] k₀ :=
    (IntermediateField.adjoinRootEquivAdjoin (ResidueField R) hθi).trans
      ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv)
  obtain ⟨P, hPmap, -, hP⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts _).mpr
        (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective (minpoly (ResidueField R) θ))) hQm
  have hPmap' : P.map (residue R) = minpoly (ResidueField R) θ := hPmap
  have hirr : Irreducible (P.map (residue R)) := by rw [hPmap']; exact hQirr
  have hsep : (P.map (residue R)).Separable := by rw [hPmap']; exact hQsep

  letI := isLocalRing hP hirr
  haveI := nontrivial hirr
  haveI : Module.Finite R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hP).finite
  haveI : Module.Free R (AdjoinRoot P) := .of_basis (AdjoinRoot.powerBasis' hP).basis
  haveI : IsNoetherianRing (AdjoinRoot P) := isNoetherian_of_tower R inferInstance
  haveI hlh : IsLocalHom (algebraMap R (AdjoinRoot P)) := isLocalHom hP hirr
  haveI : IsDomain (AdjoinRoot P) := isDomain hP hirr
  have hinj : Function.Injective (algebraMap R (AdjoinRoot P)) := FaithfulSMul.algebraMap_injective R _
  haveI : CharZero (AdjoinRoot P) := charZero_of_injective_algebraMap hinj

  have hmR : maximalIdeal R = Ideal.span {(p : R)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hunif
  have hmax : maximalIdeal (AdjoinRoot P) = Ideal.span {(p : AdjoinRoot P)} := by
    rw [maximalIdeal_eq hP hirr, m0, hmR, Ideal.map_span, Set.image_singleton, ← AdjoinRoot.algebraMap_eq, map_natCast]
  have hp0' : (p : AdjoinRoot P) ≠ 0 := by
    rw [← map_natCast (algebraMap R (AdjoinRoot P))]
    exact (map_ne_zero_iff _ hinj).mpr hunif.ne_zero
  have hnf : ¬ IsField (AdjoinRoot P) := fun hfld => by
    have h := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfld
    rw [hmax, Ideal.span_singleton_eq_bot] at h
    exact hp0' h
  haveI hdvr : IsDiscreteValuationRing (AdjoinRoot P) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot P) hnf).out 0 4).mpr
      (⟨⟨(p : AdjoinRoot P), by rw [hmax, Ideal.submodule_span_eq]⟩⟩ :
        Submodule.IsPrincipal (maximalIdeal (AdjoinRoot P)))
  have hirr' : Irreducible (p : AdjoinRoot P) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax

  haveI hcomp : IsAdicComplete (maximalIdeal (AdjoinRoot P)) (AdjoinRoot P) :=
    IsLocalRing.isAdicComplete_of_module_finite (𝒪 := R)

  let eres : ResidueField (AdjoinRoot P) ≃+* AdjoinRoot (P.map (residue R)) := residueEquiv hP hirr
  have eQ' : AdjoinRoot (P.map (residue R)) ≃ₐ[ResidueField R] k₀ := by rw [hPmap']; exact eQ
  let e : k₀ →+* ResidueField (AdjoinRoot P) := eres.symm.toRingHom.comp eQ'.symm.toAlgHom.toRingHom
  have he : e.comp (algebraMap (ResidueField R) k₀) = ResidueField.map (algebraMap R (AdjoinRoot P)) := by
    apply RingHom.ext
    intro x
    obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal R) x

    have hrhs : ResidueField.map (algebraMap R (AdjoinRoot P)) (Ideal.Quotient.mk (maximalIdeal R) x₀)
        = residue (AdjoinRoot P) (AdjoinRoot.mk P (C x₀)) := by
      show ResidueField.map (algebraMap R (AdjoinRoot P)) (residue R x₀) = _
      rw [ResidueField.map_residue, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C]
    rw [hrhs]

    show eres.symm (eQ'.symm.toAlgHom (algebraMap (ResidueField R) k₀ (Ideal.Quotient.mk _ x₀))) = _
    apply eres.injective
    rw [RingEquiv.apply_symm_apply, AlgHom.commutes, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C]
    have h2 : eres (residue (AdjoinRoot P) (AdjoinRoot.mk P (C x₀)))
        = AdjoinRoot.mk (P.map (residue R)) ((C x₀).map (residue R)) := residueEquiv_residue_mk hP hirr (C x₀)
    rw [h2, Polynomial.map_C]
    rfl
  exact ⟨AdjoinRoot P, inferInstance, inferInstance, hdvr, inferInstance, inferInstance, inferInstance,
    inferInstance, etale hP hirr hsep, hlh, hcomp, hirr', e, he⟩

end S_IsDiscreteValuationRing_exists_finite_etale_isAdicComplete_residueField_algHom
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_finite_etale_isAdicComplete_residueField_algHom (solution)
