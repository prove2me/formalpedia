-- Prove2me | solution 1 for NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1006134f-b83a-560d-ad28-a0d41f25b323

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace P2mIdxOne

open IsLocalRing

section Field

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]

theorem isRegularLocalRing_localization_of_smooth [Algebra.Smooth k B] (q : Ideal B) [hq : q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    show (algebraMap k B).Smooth
    rw [RingHom.Smooth]
    convert (inferInstance : Algebra.Smooth k B)
    exact Algebra.algebra_ext _ _ fun _ => rfl
  have h := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk
    (f := Spec.map (CommRingCat.ofHom (algebraMap k B))) (⟨q, hq⟩ : PrimeSpectrum B)
  exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _
    (AlgebraicGeometry.StructureSheaf.stalkIso B (⟨q, hq⟩ : PrimeSpectrum B)).toRingEquiv.symm

theorem isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero (S : Type u) [CommRing S]
    [IsRegularLocalRing S] (h : ringKrullDim S = 0) : IsField S := by
  have hsp : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) = ringKrullDim S :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  rw [h] at hsp
  have h0 : (maximalIdeal S).spanFinrank = 0 := by exact_mod_cast hsp
  have hbot : maximalIdeal S = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot

theorem isField_localization_of_smooth_of_minimal [Algebra.Smooth k B] (q : Ideal B) [hq : q.IsPrime]
    (hmin : q ∈ minimalPrimes B) : IsField (Localization.AtPrime q) := by
  haveI := isRegularLocalRing_localization_of_smooth (k := k) q
  apply isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
    Ideal.height_eq_zero_iff.mpr hmin]
  rfl

end Field

end P2mIdxOne

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (ζ : Z) (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hgen : ∀ y : Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ)
    [Algebra R (Z.presheaf.stalk ζ)]
    (halg : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ)))) :
    ∃ (_ : IsDomain (Z.presheaf.stalk ζ)) (_ : IsDiscreteValuationRing (Z.presheaf.stalk ζ))
      (_ : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ))),
      IsIndexOneExtension R (Z.presheaf.stalk ζ) := by
  classical

  obtain ⟨hdom, hdvr⟩ :=
    AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R z ζ hζ hgen
  haveI := hdom
  haveI := hdvr
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R

  let g : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ (z.base ζ) trivial
  let φ : CommRingCat.of R ⟶ Z.presheaf.stalk ζ := g ≫ z.stalkMap ζ
  have hfac : Z.fromSpecStalk ζ ≫ z = Spec.map φ := by
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk z, Spec.fromSpecStalk_eq]
  have hφ : algebraMap R (Z.presheaf.stalk ζ) = φ.hom := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ))) = Spec.map φ :=
      halg.symm.trans hfac
    have h2 := Spec.map_injective h1
    exact congrArg (fun f => f.hom) h2
  have hbase : ∀ 𝔮 : PrimeSpectrum (Z.presheaf.stalk ζ),
      z.base ((Z.fromSpecStalk ζ).base 𝔮) = (Spec.map φ).base 𝔮 := fun 𝔮 => by
    rw [← hfac]; rfl
  have hcomapq : ∀ 𝔮 : PrimeSpectrum (Z.presheaf.stalk ζ),
      ((Spec.map φ).base 𝔮).asIdeal = 𝔮.asIdeal.comap φ.hom := fun _ => rfl

  have hcomap : (IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ)).comap (algebraMap R (Z.presheaf.stalk ζ)) =
      IsLocalRing.maximalIdeal R := by
    rw [hφ]
    change (IsLocalRing.closedPoint (Z.presheaf.stalk ζ)).asIdeal.comap φ.hom = _
    rw [← hcomapq, ← hbase, Scheme.fromSpecStalk_closedPoint, hζ]
    rfl
  haveI hlh : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hmem : a ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr hna
    rw [← hcomap, Ideal.mem_comap] at hmem
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) ha
  have hϖm : algebraMap R (Z.presheaf.stalk ζ) ϖ ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ) := by
    rw [← Ideal.mem_comap, hcomap]
    exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit

  have hgreg : IsSMulRegular ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ)) (g.hom ϖ) := by
    letI : Algebra Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ)) :=
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (z.base ζ) trivial).hom.toAlgebra
    haveI := (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_stalk ⟨z.base ζ, trivial⟩
    haveI : IsDomain Γ(Spec (CommRingCat.of R), ⊤) :=
      Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
    have hle := ((isAffineOpen_top (Spec (CommRingCat.of R))).primeIdealOf
      ⟨z.base ζ, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
    haveI : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ)) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
    have hne : g.hom ϖ ≠ 0 := by
      intro h0
      have hinj := IsLocalization.injective ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ)) hle
      have h0' : algebraMap Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ))
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)
          = algebraMap Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ)) 0 := by
        rw [map_zero]; exact h0
      have := hinj h0'
      exact hϖ.ne_zero ((Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
        (by rw [map_zero]; exact this))
    exact (IsRegular.of_ne_zero hne).left.isSMulRegular
  haveI hflat : (z.stalkMap ζ).hom.Flat := Flat.stalkMap z ζ
  have hreg : IsSMulRegular (Z.presheaf.stalk ζ) (φ.hom ϖ) := by
    letI := (z.stalkMap ζ).hom.toAlgebra
    haveI : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ)) (Z.presheaf.stalk ζ) := hflat
    exact hgreg.of_flat
  have hne0 : algebraMap R (Z.presheaf.stalk ζ) ϖ ≠ 0 := by
    rw [hφ]
    intro h0
    have h1 : φ.hom ϖ * 1 = φ.hom ϖ * 0 := by rw [h0, zero_mul, zero_mul]
    exact one_ne_zero (hreg h1)

  obtain ⟨_, ⟨V, hV, rfl⟩, hζV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ζ) isOpen_univ
  have hVU : (V : Z.Opens) ≤ z ⁻¹ᵁ ⊤ := le_top
  have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of R)).Opens) := isAffineOpen_top _
  have hψ : (z.appLE ⊤ V hVU).hom.Smooth := z.smooth_appLE hU hV hVU
  have hιR : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  letI algRA : Algebra R Γ(Z, V) := ((z.appLE ⊤ V hVU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
  haveI hsmA : Algebra.Smooth R Γ(Z, V) := RingHom.Smooth.comp (RingHom.Smooth.of_bijective hιR) hψ
  letI algAO : Algebra Γ(Z, V) (Z.presheaf.stalk ζ) := Z.presheaf.algebra_section_stalk ⟨ζ, hζV⟩
  haveI hlocO := hV.isLocalization_stalk ⟨ζ, hζV⟩
  have halgRA : ∀ r : R, algebraMap R Γ(Z, V) r = (z.appLE ⊤ V hVU).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) :=
    fun r => rfl
  have halgAO : ∀ a : Γ(Z, V), algebraMap Γ(Z, V) (Z.presheaf.stalk ζ) a = (Z.presheaf.germ V ζ hζV).hom a :=
    fun a => rfl
  haveI htower : IsScalarTower R Γ(Z, V) (Z.presheaf.stalk ζ) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [halgAO, halgRA, hφ]
    show (z.stalkMap ζ).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (z.base ζ) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    rw [Scheme.Hom.germ_stalkMap_apply]
    simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      Z.presheaf.germ_res_apply]

  have hϖmR : ϖ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit

  have h𝔭 : (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal = (IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ)).comap (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ)) :=
    (IsLocalization.AtPrime.under_maximalIdeal (Z.presheaf.stalk ζ) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal).symm
  have h𝔭R : (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal.comap (algebraMap R Γ(Z, V)) = IsLocalRing.maximalIdeal R := by
    rw [h𝔭, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hcomap]
  have h𝔞𝔭 : ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))) ≤ (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal := by
    rw [Ideal.map_le_iff_le_comap, h𝔭R]
  letI kfield : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  haveI : Algebra.FormallySmooth R Γ(Z, V) := hsmA.formallySmooth
  haveI : Algebra.FinitePresentation R Γ(Z, V) := hsmA.finitePresentation
  haveI hsmB : Algebra.Smooth (R ⧸ IsLocalRing.maximalIdeal R) (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) :=
    ⟨Algebra.FormallySmooth.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Γ(Z, V) (IsLocalRing.maximalIdeal R)).symm,
     Algebra.FinitePresentation.equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Γ(Z, V) (IsLocalRing.maximalIdeal R)).symm⟩
  haveI hq' : (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact h𝔞𝔭)
  have hcQQ : (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal).comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) = (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    have : Ideal.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) ⊥ = ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))) := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [this]
    exact sup_eq_left.mpr h𝔞𝔭

  have hmin : (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal) ∈ minimalPrimes (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) := by
    rw [minimalPrimes_eq_minimals]
    refine ⟨hq', fun Q' hQ' hle => ?_⟩
    haveI := hQ'
    haveI hQp : (Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))))).IsPrime := Ideal.comap_isPrime _ _
    have hQle : Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) ≤ (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal := by
      rw [← hcQQ]; exact Ideal.comap_mono hle
    have hdisj : Disjoint (((hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal.primeCompl : Submonoid Γ(Z, V)) : Set Γ(Z, V)) ↑(Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))))) := by
      rw [Set.disjoint_left]
      intro x hx hxQ
      exact hx (hQle hxQ)
    have hQO : ((Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal.primeCompl (Z.presheaf.stalk ζ) _ hQp hdisj
    have hQO_ne : (Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ)) ≠ ⊥ := by
      intro h0
      have hmem : algebraMap R (Z.presheaf.stalk ζ) ϖ ∈ (Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ)) := by
        rw [IsScalarTower.algebraMap_apply R Γ(Z, V) (Z.presheaf.stalk ζ)]
        apply Ideal.mem_map_of_mem
        have h1 : algebraMap R Γ(Z, V) ϖ ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))) := Ideal.mem_map_of_mem _ hϖmR
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr h1]
        exact Q'.zero_mem
      rw [h0] at hmem
      exact hne0 (Ideal.mem_bot.mp hmem)
    have hQO_max : (Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ)) =
        IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ) :=
      IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hQO_ne hQO)
    have hQeq : Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) = (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal := by
      have h1 := IsLocalization.under_map_of_isPrime_disjoint (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal.primeCompl (Z.presheaf.stalk ζ) hQp hdisj
      rw [hQO_max, Ideal.under_def] at h1
      rw [← h1, h𝔭]
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) Ideal.Quotient.mk_surjective Q', hQeq]

  have hfield : IsField (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) :=
    P2mIdxOne.isField_localization_of_smooth_of_minimal (k := (R ⧸ IsLocalRing.maximalIdeal R)) (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal) hmin

  have hsub : Algebra.algebraMapSubmonoid (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal.primeCompl = (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal).primeCompl := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hx
      intro hmem
      apply ha
      show a ∈ (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal
      rw [← hcQQ, Ideal.mem_comap]
      exact hmem
    · intro hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine Submonoid.mem_map.mpr ⟨a, ?_, rfl⟩
      intro ha
      exact hx (Ideal.mem_map_of_mem _ ha)
  haveI hlocOB : IsLocalization.AtPrime ((Z.presheaf.stalk ζ) ⧸ (((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ))) (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal) := by
    have h : IsLocalization (Algebra.algebraMapSubmonoid (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal.primeCompl) ((Z.presheaf.stalk ζ) ⧸ (((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ))) := inferInstance
    rwa [hsub] at h
  let eO : ((Z.presheaf.stalk ζ) ⧸ (((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ))) ≃ₐ[(Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))))] Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal) :=
    IsLocalization.algEquiv (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal).primeCompl ((Z.presheaf.stalk ζ) ⧸ (((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal))
  have hOBfield : IsField ((Z.presheaf.stalk ζ) ⧸ (((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ))) := MulEquiv.isField hfield eO.toMulEquiv

  have h𝔞O : (((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ)) = (IsLocalRing.maximalIdeal R).map (algebraMap R (Z.presheaf.stalk ζ)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R (Z.presheaf.stalk ζ)) = IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ) := by
    rw [← h𝔞O]
    exact IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hOBfield)

  haveI : Algebra.FormallySmooth (R ⧸ IsLocalRing.maximalIdeal R) (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) := hsmB.formallySmooth
  haveI : Algebra.FormallySmooth (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) :=
    Algebra.FormallySmooth.of_isLocalization (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal).primeCompl
  have hfsX : Algebra.FormallySmooth (R ⧸ IsLocalRing.maximalIdeal R) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) :=
    Algebra.FormallySmooth.comp (R ⧸ IsLocalRing.maximalIdeal R) (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal))
  letI algkX : Algebra (IsLocalRing.ResidueField R) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) :=
    (inferInstance : Algebra (R ⧸ IsLocalRing.maximalIdeal R) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)))
  have hfsX' : Algebra.FormallySmooth (IsLocalRing.ResidueField R) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) := hfsX
  let eR : Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal) ≃+* IsLocalRing.ResidueField (Z.presheaf.stalk ζ) :=
    eO.symm.toRingEquiv.trans (Ideal.quotEquivOfEq (h𝔞O.trans hmap))
  have hcomm : ∀ x : IsLocalRing.ResidueField R,
      eR (algebraMap (IsLocalRing.ResidueField R) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) x) =
        algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (Z.presheaf.stalk ζ)) x := by
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    have h1 : algebraMap (IsLocalRing.ResidueField R) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) (IsLocalRing.residue R r) =
        algebraMap (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))) (algebraMap R Γ(Z, V) r)) := by
      show algebraMap (R ⧸ IsLocalRing.maximalIdeal R) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) (Ideal.Quotient.mk _ r) = _
      rw [IsScalarTower.algebraMap_apply (R ⧸ IsLocalRing.maximalIdeal R) (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal))]
      rfl
    rw [h1]
    show Ideal.quotEquivOfEq (h𝔞O.trans hmap) (eO.symm (algebraMap (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) _)) = _
    rw [AlgEquiv.commutes]
    show Ideal.quotEquivOfEq (h𝔞O.trans hmap) (Ideal.Quotient.mk _ (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ) (algebraMap R Γ(Z, V) r))) = _
    rw [Ideal.quotEquivOfEq_mk, ← IsScalarTower.algebraMap_apply]
    rfl
  let eA : Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal) ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField (Z.presheaf.stalk ζ) :=
    AlgEquiv.ofRingEquiv (f := eR) hcomm
  have hfs : Algebra.FormallySmooth (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField (Z.presheaf.stalk ζ)) :=
    Algebra.FormallySmooth.of_equiv eA
  exact ⟨hdom, hdvr, hlh, ⟨hmap, hfs⟩⟩

end S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
end P2MW
export P2MW.S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes (solution)
