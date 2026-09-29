-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.not_smooth_pullback_snd_toBase_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4549d1be-54bb-5c23-abcd-b6f358b9adfd

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_XHDRModelAtP_connectedSpace_pullback_toBase_specMap_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_not_smooth_pullback_snd_toBase_of_charP
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_not_smooth_pullback_snd_toBase_of_charP.ModularCurve ModularCurve.XHDRLevel NeronModelInfra"
open scoped MatrixGroups

open IsLocalRing Topology

namespace NSDR

theorem primeSpectrum_pigeonhole {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (q₁ q₂ q₃ : PrimeSpectrum R) : q₁ = q₂ ∨ q₁ = q₃ ∨ q₂ = q₃ := by
  have key : ∀ q : PrimeSpectrum R, q.asIdeal = ⊥ ∨ q.asIdeal = IsLocalRing.maximalIdeal R := by
    intro q
    by_cases h : q.asIdeal = ⊥
    · exact Or.inl h
    · exact Or.inr (IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal h))
  rcases key q₁ with h₁ | h₁ <;> rcases key q₂ with h₂ | h₂ <;> rcases key q₃ with h₃ | h₃
  all_goals first
    | exact Or.inl (PrimeSpectrum.ext (h₁.trans h₂.symm))
    | exact Or.inr (Or.inl (PrimeSpectrum.ext (h₁.trans h₃.symm)))
    | exact Or.inr (Or.inr (PrimeSpectrum.ext (h₂.trans h₃.symm)))

theorem isClosed_singleton_or_eq_genericPoint {P : Scheme} [IsIntegral P] [JacobsonSpace P]
    (hdvr : ∀ x : P, IsClosed ({x} : Set P) → IsDiscreteValuationRing (P.presheaf.stalk x))
    (c : P) : IsClosed ({c} : Set P) ∨ c = genericPoint P := by
  by_contra h
  push Not at h
  obtain ⟨hc, hcξ⟩ := h

  obtain ⟨x, hxZ, hx⟩ := nonempty_inter_closedPoints (X := P) (Z := closure {c})
    ⟨c, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  rw [mem_closedPoints_iff] at hx
  have hcx : c ⤳ x := specializes_iff_mem_closure.mpr hxZ
  have hξx : genericPoint P ⤳ x := (genericPoint_spec P).specializes (Set.mem_univ x)
  have hxc : x ≠ c := by rintro rfl; exact hc hx
  have hξc : genericPoint P ≠ c := fun e => hcξ e.symm
  have hξx' : genericPoint P ≠ x := by
    rintro e
    apply hcξ

    have h1 : closure ({genericPoint P} : Set P) = Set.univ := genericPoint_closure P
    rw [e, hx.closure_eq] at h1
    have : c ∈ ({x} : Set P) := by rw [h1]; exact Set.mem_univ c
    rw [Set.mem_singleton_iff] at this
    rw [this, e]

  haveI := hdvr x hx
  have hr : ∀ y : P, y ⤳ x → ∃ q : Spec (P.presheaf.stalk x), (P.fromSpecStalk x).base q = y := by
    intro y hy
    have : y ∈ Set.range (P.fromSpecStalk x).base := by rw [Scheme.range_fromSpecStalk]; exact hy
    exact this
  obtain ⟨q₁, hq₁⟩ := hr _ hcx
  obtain ⟨q₂, hq₂⟩ := hr _ hξx
  obtain ⟨q₃, hq₃⟩ := hr _ (le_refl x : x ⤳ x)
  rcases primeSpectrum_pigeonhole q₁ q₂ q₃ with e | e | e
  · exact hξc (hq₂.symm.trans ((congrArg (fun q => (P.fromSpecStalk x).base q) e.symm).trans hq₁))
  · exact hxc (hq₃.symm.trans ((congrArg (fun q => (P.fromSpecStalk x).base q) e.symm).trans hq₁))
  · exact hξx' (hq₂.symm.trans ((congrArg (fun q => (P.fromSpecStalk x).base q) e).trans hq₃))

theorem false_of_range_eq_univ {P X : Scheme} [IsIntegral P] [JacobsonSpace P]
    (hdvr : ∀ x : P, IsClosed ({x} : Set P) → IsDiscreteValuationRing (P.presheaf.stalk x))
    (i j : P ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : Set.range i.base = Set.univ) (hij : Set.range j.base ≠ Set.range i.base) : False := by
  have hie := i.isClosedEmbedding
  have hje := j.isClosedEmbedding
  set ξ := genericPoint P with hξ

  have hrange : ∀ (k : P ⟶ X), IsClosedEmbedding k.base → Set.range k.base = closure {k.base ξ} := by
    intro k hk
    rw [← Set.image_singleton, hk.closure_image_eq, genericPoint_closure, Set.image_univ]

  obtain ⟨c, hc⟩ : j.base ξ ∈ Set.range i.base := by rw [hi]; exact Set.mem_univ _
  have hcξ : c ≠ ξ := by
    intro e
    apply hij
    rw [hrange j hje, hrange i hie, ← hc, e]
  rcases isClosed_singleton_or_eq_genericPoint hdvr c with hcl | hcl
  ·
    have hj : Set.range j.base = {j.base ξ} := by
      rw [hrange j hje, ← hc, ← Set.image_singleton, hie.closure_image_eq, hcl.closure_eq, Set.image_singleton]
    have : j.base c ∈ ({j.base ξ} : Set X) := hj ▸ Set.mem_range_self c
    exact hcξ (hje.injective (Set.mem_singleton_iff.mp this))
  · exact hcξ hcl

theorem false_of_jointly_surjective {P X : Scheme} [IsIntegral P] [JacobsonSpace P] [IrreducibleSpace X]
    (hdvr : ∀ x : P, IsClosed ({x} : Set P) → IsDiscreteValuationRing (P.presheaf.stalk x))
    (i j : P ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (hcov : ∀ x : X, x ∈ Set.range i.base ∨ x ∈ Set.range j.base)
    (hne : Set.range i.base ≠ Set.range j.base) : False := by
  have hA : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  have hB : IsClosed (Set.range j.base) := j.isClosedEmbedding.isClosed_range
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
      _ _ hA hB (fun x _ => hcov x)) with h | h
  · exact false_of_range_eq_univ hdvr i j (Set.eq_univ_of_univ_subset h) hne.symm
  · exact false_of_range_eq_univ hdvr j i (Set.eq_univ_of_univ_subset h) hne

end NSDR

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC jqModC XHDRModelAtP.connectedSpace_pullback_toBase_specMap_of_isAlgClosed DRLevel.exists_place_residueField_ringHom_comp_eq"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "comp_jointly_surjective efib comp_isClosedImmersion Mfib range_comp_ne comp connectedSpace_pullback_toBase_specMap_of_isAlgClosed"
namespace NonsmoothH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

theorem irreducibleSpace_pullback_of_comp {R : Type} [CommRing R] {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of R))
    {L L' : Type} [Field L] [Field L'] (ψ : R →+* L) (φ : L →+* L')
    [IrreducibleSpace ↥(pullback c (Spec.map (CommRingCat.ofHom (φ.comp ψ))))] :
    IrreducibleSpace ↥(pullback c (Spec.map (CommRingCat.ofHom ψ))) := by
  let g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom ψ)
  let g' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of L) := Spec.map (CommRingCat.ofHom φ)
  have heq : Spec.map (CommRingCat.ofHom (φ.comp ψ)) = g' ≫ g := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : Surjective g' := ⟨fun x => by
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of L')))
    exact ⟨y, Subsingleton.elim _ _⟩⟩
  let e : pullback c (Spec.map (CommRingCat.ofHom (φ.comp ψ))) ⟶ pullback c g :=
    (pullback.congrHom rfl heq).hom ≫ (pullbackLeftPullbackSndIso c g g').inv ≫ pullback.fst (pullback.snd c g) g'
  haveI : Surjective (pullback.fst (pullback.snd c g) g') := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : Surjective e := inferInstance
  exact e.surjective.irreducibleSpace e.continuous

end ModularCurve.XHDRModelAtP.NonsmoothH

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R p))),
      ¬ Smooth (pullback.snd (toBase p (ΓM M H) hj) x) := by
  intro k _ _ _ x hsm

  obtain ⟨toκ, rfl⟩ : ∃ toκ : R p →+* k, x = Spec.map (CommRingCat.ofHom toκ) :=
    ⟨(Spec.preimage x).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  haveI := hsm

  letI : Algebra (R p) k := toκ.toAlgebra
  haveI : ConnectedSpace ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) :=
    ModularCurve.XHDRModelAtP.connectedSpace_pullback_toBase_specMap_of_isAlgClosed p M H hpM hj 𝔛 k
  haveI : IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) :=
    AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace
      (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)))

  obtain ⟨A, hA, hch, hac, ρ, hρ, φ, hφ⟩ := ModularCurve.DRLevel.exists_place_residueField_ringHom_comp_eq p k toκ
  haveI := hch
  haveI := hac

  haveI : IrreducibleSpace ↥(pullback (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (φ.comp ((residue ↥A).comp ρ))))) := by
    rw [hφ]; infer_instance
  haveI : IrreducibleSpace ↥(fibre (Γ := ΓM M H) (hj := hj) ((residue ↥A).comp ρ)) :=
    ModularCurve.XHDRModelAtP.NonsmoothH.irreducibleSpace_pullback_of_comp (toBase p (ΓM M H) hj) ((residue ↥A).comp ρ) φ

  let P := (𝔛.Mfib A hA ρ hρ).C
  haveI : Smooth (𝔛.Mfib A hA ρ hρ).toBase := SmoothOfRelativeDimension.smooth 1 _
  haveI : JacobsonSpace ↥P := LocallyOfFiniteType.jacobsonSpace (𝔛.Mfib A hA ρ hρ).toBase
  have hdvr : ∀ y : ↥P, IsClosed ({y} : Set ↥P) → IsDiscreteValuationRing (P.presheaf.stalk y) := fun y hy =>
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed (𝔛.Mfib A hA ρ hρ).toBase y hy
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  let i : P ⟶ fibre (Γ := ΓM M H) (hj := hj) ((residue ↥A).comp ρ) := 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0
  let j : P ⟶ fibre (Γ := ΓM M H) (hj := hj) ((residue ↥A).comp ρ) := 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1
  haveI : IsClosedImmersion i := inferInstance
  haveI : IsClosedImmersion j := inferInstance
  have hsurj : Function.Surjective (𝔛.efib A hA ρ hρ).base := (𝔛.efib A hA ρ hρ).surjective
  have hri : Set.range i.base = Set.range (𝔛.comp A hA ρ hρ 0).base := by
    show Set.range ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base) = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, hsurj.range_comp]
  have hrj : Set.range j.base = Set.range (𝔛.comp A hA ρ hρ 1).base := by
    show Set.range ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base) = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, hsurj.range_comp]
  refine NSDR.false_of_jointly_surjective hdvr i j (fun y => ?_) ?_
  · rw [hri, hrj]; exact 𝔛.comp_jointly_surjective A hA ρ hρ y
  · rw [hri, hrj]; exact 𝔛.range_comp_ne A hA ρ hρ

end S_ModularCurve_XHDRModelAtP_not_smooth_pullback_snd_toBase_of_charP
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_not_smooth_pullback_snd_toBase_of_charP (solution)
