-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7843def5-5a82-5e38-bd2c-9c7450abf37a

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt.GoodReductionJacobian"
open scoped nonZeroDivisors

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw RelativeGroupLaw.exists_injective_specialize_isTorsionPoint_of_smooth"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul IsTorsionPoint genericFibre fibre exists_injective_specialize_isTorsionPoint_of_smooth"
namespace TorsionSpecializationDedekind
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section EtaleNbhd

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P]

theorem exists_formallyUnramified_away :
    ∃ f : S, f ∉ P ∧ Algebra.FormallyUnramified R (Localization.Away f) := by
  have hmem : (⟨P, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.unramifiedLocus R S := by
    change Algebra.IsUnramifiedAt R P
    infer_instance
  obtain ⟨v, ⟨f, rfl⟩, hfv, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem
      Algebra.isOpen_unramifiedLocus
  refine ⟨f, ?_, Algebra.basicOpen_subset_unramifiedLocus_iff.mp hsub⟩
  simpa using hfv

variable (f : S)

theorem smooth_specMap_away [Algebra.FormallyUnramified R (Localization.Away f)] :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) := by
  haveI : Module.Flat R (Localization.Away f) := Module.Flat.trans R S (Localization.Away f)
  haveI : Algebra.FiniteType R (Localization.Away f) :=
    Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  haveI : Algebra.FinitePresentation R (Localization.Away f) :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  haveI : Algebra.Etale R (Localization.Away f) := Algebra.Etale.of_formallyUnramified_of_flat
  haveI : Algebra.Smooth R (Localization.Away f) := inferInstance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R (Localization.Away f)).Smooth
  rw [RingHom.smooth_algebraMap]
  infer_instance

end EtaleNbhd

section GenericFibre

variable (R : Type u) [CommRing R] [IsDomain R]
  (S : Type u) [CommRing S] [IsDomain S] [Algebra R S]
  (L : Type u) [Field L] [Algebra S L] [Algebra R L]
  [IsScalarTower R S L] [IsFractionRing S L] [IsIntegralClosure S R L]
  (f : S) (hf : f ≠ 0)

noncomputable def awayToField : Localization.Away f →+* L :=
  IsLocalization.Away.lift f (g := algebraMap S L)
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr hf))

theorem awayToField_comp : (awayToField S L f hf).comp (algebraMap S (Localization.Away f)) = algebraMap S L :=
  IsLocalization.Away.lift_comp f _

theorem awayToField_injective : Function.Injective (awayToField S L f hf) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) x
  have h := IsLocalization.mk'_spec (Localization.Away f) s m
  have h' := congrArg (awayToField S L f hf) h
  rw [map_mul, hx, zero_mul, ← RingHom.comp_apply, awayToField_comp] at h'
  have hs : s = 0 := (map_eq_zero_iff _ (IsFractionRing.injective S L)).mp h'.symm
  subst hs
  change IsLocalization.mk' (Localization.Away f) 0 m = 0
  exact IsLocalization.mk'_zero _

theorem isLocalization_away (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [IsScalarTower R K L] [Algebra.IsAlgebraic K L] :
    letI : Algebra (Localization.Away f) L := (awayToField S L f hf).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away f) R⁰) L := by
  letI : Algebra (Localization.Away f) L := (awayToField S L f hf).toAlgebra
  have halg : ∀ x, algebraMap (Localization.Away f) L x = awayToField S L f hf x := fun _ => rfl
  haveI hSL : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L :=
    IsIntegralClosure.isLocalization R K L S
  have htower : ∀ s : S, algebraMap (Localization.Away f) L (algebraMap S _ s) = algebraMap S L s := by
    intro s; rw [halg, ← RingHom.comp_apply, awayToField_comp]
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    change IsUnit (algebraMap (Localization.Away f) L (algebraMap R (Localization.Away f) r))
    rw [IsScalarTower.algebraMap_apply R S (Localization.Away f), htower]
    exact IsLocalization.map_units L (M := Algebra.algebraMapSubmonoid S R⁰)
      ⟨algebraMap R S r, r, hr, rfl⟩
  · intro y
    obtain ⟨⟨s, ⟨_, r, hr, rfl⟩⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S R⁰) y
    refine ⟨⟨algebraMap S _ s, ⟨algebraMap R _ r, r, hr, rfl⟩⟩, ?_⟩
    change y * algebraMap (Localization.Away f) L (algebraMap R (Localization.Away f) r) =
      algebraMap (Localization.Away f) L (algebraMap S _ s)
    rw [IsScalarTower.algebraMap_apply R S (Localization.Away f), htower, htower]
    exact h
  · intro x₁ x₂ h
    rw [halg, halg] at h
    exact ⟨1, by rw [awayToField_injective S L f hf h]⟩

end GenericFibre

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}

theorem main (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (L : Type u) [Field L] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] [IsFractionRing S L]
    [IsIntegralClosure S R L] [Algebra.IsAlgebraic K L]
    (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : S →ₐ[R] k')
    (hψ : ∀ s : S, ψ s = 0 → s ∈ P) :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r := by

  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective R S]
    intro a b h
    have h' := congrArg (algebraMap S L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K L] at h'
    exact (IsFractionRing.injective R K) ((algebraMap K L).injective h')

  obtain ⟨f, hfP, hunr⟩ := exists_formallyUnramified_away R S P
  haveI := hunr
  have hf0 : f ≠ 0 := fun h => hfP (h ▸ P.zero_mem)
  let R' := Localization.Away f
  haveI : IsDomain R' :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) R'
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := smooth_specMap_away R S f

  letI : Algebra R' L := (awayToField S L f hf0).toAlgebra
  have halg : ∀ x, algebraMap R' L x = awayToField S L f hf0 x := fun _ => rfl
  haveI : IsScalarTower S R' L := IsScalarTower.of_algebraMap_eq (fun s => by
    rw [halg, ← RingHom.comp_apply, awayToField_comp])
  haveI : IsScalarTower R R' L := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R S R', ← IsScalarTower.algebraMap_apply S R' L,
      ← IsScalarTower.algebraMap_apply R S L])
  haveI : IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L := isLocalization_away R S L f hf0 K

  have hψf : IsUnit ((ψ : S →+* k') f) := isUnit_iff_ne_zero.mpr (fun h => hfP (hψ f h))
  let ψ₀ : R' →+* k' := IsLocalization.Away.lift f hψf
  have hψ₀ : ψ₀.comp (algebraMap S R') = (ψ : S →+* k') := IsLocalization.Away.lift_comp f hψf
  let ψ' : R' →ₐ[R] k' :=
    { ψ₀ with
      commutes' := fun r => by
        change ψ₀ (algebraMap R R' r) = algebraMap R k' r
        rw [IsScalarTower.algebraMap_apply R S R', ← RingHom.comp_apply, hψ₀]
        exact ψ.commutes r }
  obtain ⟨r, hr, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_injective_specialize_isTorsionPoint_of_smooth
      K LB hcomm hN n hn R' hsm L k' ψ'
  exact ⟨r, hr⟩

end Main

end GoodReductionJacobian.RelativeGroupLaw.TorsionSpecializationDedekind

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (L : Type u) [Field L] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] [IsFractionRing S L]
    [IsIntegralClosure S R L] [Algebra.IsAlgebraic K L]
    (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : S →ₐ[R] k')
    (hψ : ∀ s : S, ψ s = 0 → s ∈ P) :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r :=
  GoodReductionJacobian.RelativeGroupLaw.TorsionSpecializationDedekind.main K LB hcomm hN n hn S L P k' ψ hψ

end S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt (solution)
