-- Prove2me | solution 1 for ModularCurve.exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6e7b5c5b-d3a9-544d-b381-c8d0192bc7d5

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_hom_spec_comp_eq_specMap_algebraMap_and_apply_eq_of_residueField
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback
import Theorems.Thm_AlgebraicCurve_CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_exists_liesOverPrime_schemeHomOver_comp_eq_base_closedPoint_eq_of_specializes
import Theorems.Thm_ModularCurve_IsPlaceReductionModL_apply_cuspInftyBar_eq_and_eq_cuspInftyBar_of_apply_eq_of_ord_ne_zero
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_of_comap_toSubring_eq_cuspInftyFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply"

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

namespace K1f

scoped instance isFractionRing_ratLocalizedAt (p : ℕ) : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ where
  map_units := by
    rintro ⟨y, hy⟩
    have : (y : ℚ) ≠ 0 := fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hy) (Subtype.ext h)
    exact isUnit_iff_ne_zero.mpr this
  surj := by
    intro q
    refine ⟨⟨⟨(q.num : ℚ), ?_⟩, ⟨⟨(q.den : ℚ), ?_⟩, ?_⟩⟩, ?_⟩
    · exact intCast_mem _ q.num
    · exact natCast_mem _ q.den
    · refine mem_nonZeroDivisors_iff_ne_zero.mpr fun h => q.den_nz ?_
      have := congrArg Subtype.val h
      simp at this
    · show q * (q.den : ℚ) = (q.num : ℚ)
      exact Rat.mul_den_eq_num q
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa using Subtype.ext h⟩

scoped instance surjectiveOnStalks_fst_genericFibre (p : ℕ) {X : Scheme.{0}}
    (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) :
    SurjectiveOnStalks (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) := by
  haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt p)) (S := ℚ)
  infer_instance

theorem stalkMap_fst_genericFibre_surjective (p : ℕ) {X : Scheme.{0}}
    (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
    (x : ↥(pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))) :
    Function.Surjective ((pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).stalkMap x).hom :=
  (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).stalkMap_surjective x

end K1f
p2m_reactivate "P2MW.S_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero.K1f"

namespace K1f

theorem exists_section_comp_iso_fst_eq_of_comp_eq
    {X B T M : Scheme.{u}} (c : X ⟶ B) (g : T ⟶ B) (toBase : M ⟶ T)
    (e : M ⟶ pullback c g) [IsIso e] (he : e ≫ pullback.snd c g = toBase)
    (z : T ⟶ X) (hz : z ≫ c = g) :
    ∃ x : {q : T ⟶ M // q ≫ toBase = 𝟙 T}, x.1 ≫ e ≫ pullback.fst c g = z := by
  have hz' : z ≫ c = 𝟙 T ≫ g := by rw [hz, Category.id_comp]
  refine ⟨⟨pullback.lift z (𝟙 T) hz' ≫ inv e, ?_⟩, ?_⟩
  · rw [Category.assoc, ← he, IsIso.inv_hom_id_assoc, pullback.lift_snd]
  · show (pullback.lift z (𝟙 T) hz' ≫ inv e) ≫ e ≫ pullback.fst c g = z
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

theorem exists_section_comp_iso_fst_eq_of_comp_eq'
    {X B T M : Scheme.{u}} (c : X ⟶ B) (g : T ⟶ B) (toBase : M ⟶ T)
    (e : M ⟶ pullback c g) (hiso : IsIso e) (he : e ≫ pullback.snd c g = toBase)
    (z : T ⟶ X) (hz : z ≫ c = g) :
    ∃ x : {q : T ⟶ M // q ≫ toBase = 𝟙 T}, x.1 ≫ e ≫ pullback.fst c g = z :=
  haveI := hiso
  exists_section_comp_iso_fst_eq_of_comp_eq c g toBase e he z hz

theorem specMap_ofHom_comp_specMap_ofHom {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (ψ : R →+* S) (φ : S →+* T) :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ψ) = Spec.map (CommRingCat.ofHom (φ.comp ψ)) := by
  rw [← Spec.map_comp]; rfl

end K1f
p2m_reactivate "P2MW.S_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero.K1f"

namespace K1f

theorem exists_surjective_residueField_of_section
    {X Y : Scheme.{u}} (c : X ⟶ Y) (ε : Y ⟶ X) (hε : ε ≫ c = 𝟙 Y) (y : Y) :
    ∃ π : Y.residueField y →+* X.residueField (ε.base y), Function.Surjective π := by
  have hcx : c.base (ε.base y) = y := by
    change (ε ≫ c).base y = y
    rw [hε]; rfl

  let π₀ : Y.residueField y ⟶ X.residueField (ε.base y) :=
    (Y.residueFieldCongr hcx).inv ≫ c.residueFieldMap (ε.base y)
  let r : X.residueField (ε.base y) ⟶ Y.residueField y := ε.residueFieldMap y

  have key : c.residueFieldMap (ε.base y) ≫ r = (Y.residueFieldCongr hcx).hom := by
    have h1 := Scheme.Hom.residueFieldMap_congr hε y
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_id] at h1

    erw [Category.comp_id] at h1
    exact h1
  have hcomp : π₀ ≫ r = 𝟙 _ := by
    simp only [π₀, Category.assoc, key, Iso.inv_hom_id]

  have hr_inj : Function.Injective r.hom := RingHom.injective r.hom
  have hleft : Function.LeftInverse r.hom π₀.hom := fun a => by
    change (π₀ ≫ r).hom a = a
    rw [hcomp]; rfl
  refine ⟨π₀.hom, fun b => ⟨r.hom b, hr_inj ?_⟩⟩
  exact hleft (r.hom b)

theorem span_natCast_isPrime (p : ℕ) [hp : Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)

theorem inv_intCast_mem_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] (b : ℤ) (hpb : ¬ (p : ℤ) ∣ b) :
    ((b : ℚ))⁻¹ ∈ GaloisRep.ratLocalizedAt p := by
  have hb0 : b ≠ 0 := fun h => hpb (h ▸ dvd_zero _)
  show (((b : ℚ))⁻¹).den.Coprime p
  rw [Rat.inv_intCast_den, if_neg hb0]
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr (fun h => hpb (Int.ofNat_dvd_left.mpr h)))

theorem isLocalization_atPrime_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] :
    @IsLocalization.AtPrime ℤ _ ↥(GaloisRep.ratLocalizedAt p) _ _ (Ideal.span {(p : ℤ)}) (span_natCast_isPrime p) := by
  letI := span_natCast_isPrime p
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨b, hb⟩
    have hpb : ¬ (p : ℤ) ∣ b := fun h => hb (Ideal.mem_span_singleton.mpr h)
    have hb0 : b ≠ 0 := fun h => hpb (h ▸ dvd_zero _)
    refine ⟨⟨algebraMap ℤ ↥(GaloisRep.ratLocalizedAt p) b, ⟨((b : ℚ))⁻¹, inv_intCast_mem_ratLocalizedAt p b hpb⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext; show ((b : ℚ)) * ((b : ℚ))⁻¹ = 1; exact mul_inv_cancel₀ (by exact_mod_cast hb0)
    · apply Subtype.ext; show ((b : ℚ))⁻¹ * ((b : ℚ)) = 1; exact inv_mul_cancel₀ (by exact_mod_cast hb0)
  · intro r
    have hden : ((r : ℚ).den : ℤ) ∈ (Ideal.span {(p : ℤ)}).primeCompl := by
      intro h
      replace h : ((r : ℚ).den : ℤ) ∈ Ideal.span {(p : ℤ)} := h
      rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast] at h
      have hcop : ((r : ℚ)).den.Coprime p := r.2
      exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm h)
    refine ⟨⟨(r : ℚ).num, ⟨_, hden⟩⟩, ?_⟩
    apply Subtype.ext
    show (r : ℚ) * (((r : ℚ).den : ℤ) : ℚ) = (((r : ℚ).num : ℤ) : ℚ)
    push_cast
    exact Rat.mul_den_eq_num (r : ℚ)
  · intro x y h
    exact ⟨1, by simpa using h⟩

theorem not_isUnit_natCast_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] :
    ¬ IsUnit ((p : ↥(GaloisRep.ratLocalizedAt p))) := by
  rintro ⟨u, hu⟩
  have hinv : ((u⁻¹ : (↥(GaloisRep.ratLocalizedAt p))ˣ) : ↥(GaloisRep.ratLocalizedAt p)) * (p : ↥(GaloisRep.ratLocalizedAt p)) = 1 := by
    rw [← hu, Units.inv_mul]
  have hq : (((u⁻¹ : (↥(GaloisRep.ratLocalizedAt p))ˣ) : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = ((p : ℚ))⁻¹ := by
    have := congrArg Subtype.val hinv
    simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
    exact eq_inv_of_mul_eq_one_left this
  have hmem : ((p : ℚ))⁻¹ ∈ GaloisRep.ratLocalizedAt p := by rw [← hq]; exact Subtype.mem _
  have hden : (((p : ℚ))⁻¹).den.Coprime p := hmem
  rw [Rat.inv_natCast_den, if_neg hp.out.ne_zero] at hden
  exact hp.out.one_lt.ne' ((Nat.coprime_self p).mp hden)

theorem exists_surjective_zmod_residueField_spec_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime]
    (s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
    (hs : IsClosed ({s} : Set (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))))) :
    ∃ π : ZMod p →+* (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).residueField s, Function.Surjective π := by
  classical
  letI := span_natCast_isPrime p
  letI := isLocalization_atPrime_ratLocalizedAt p
  haveI : IsLocalRing ↥(GaloisRep.ratLocalizedAt p) :=
    IsLocalization.AtPrime.isLocalRing ↥(GaloisRep.ratLocalizedAt p) (Ideal.span {(p : ℤ)})

  have hs' : s = IsLocalRing.closedPoint ↥(GaloisRep.ratLocalizedAt p) :=
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal s).mp hs))
  subst hs'

  let e : IsLocalRing.ResidueField ((Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.stalk
      (IsLocalRing.closedPoint ↥(GaloisRep.ratLocalizedAt p))) ≃+* IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p) :=
    IsLocalRing.ResidueField.mapEquiv (stalkClosedPointIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).commRingCatIsoToRingEquiv

  have hp0 : (p : IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)), IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr (not_isUnit_natCast_ratLocalizedAt p)
  haveI : CharP (IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p)) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).mpr hp0
  let π₀ : ZMod p →+* IsLocalRing.ResidueField ↥(GaloisRep.ratLocalizedAt p) := ZMod.castHom (dvd_refl p) _
  have hπ₀ : Function.Surjective π₀ := by
    intro t
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective t

    have hrd : r * (((r : ℚ).den : ℤ) : ↥(GaloisRep.ratLocalizedAt p)) = (((r : ℚ).num : ℤ) : ↥(GaloisRep.ratLocalizedAt p)) := by
      apply Subtype.ext
      simp only [Subring.coe_mul, Subring.coe_intCast]
      push_cast
      exact Rat.mul_den_eq_num (r : ℚ)
    have hcop : ((r : ℚ)).den.Coprime p := r.2
    have hpd : ¬ (p : ℤ) ∣ ((r : ℚ).den : ℤ) := by
      rw [Int.natCast_dvd_natCast]
      exact fun h => hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm h)
    have hden_unit : IsUnit ((((r : ℚ).den : ℤ) : ↥(GaloisRep.ratLocalizedAt p))) := by
      refine ⟨⟨_, ⟨(((((r : ℚ).den : ℤ)) : ℚ))⁻¹, inv_intCast_mem_ratLocalizedAt p _ hpd⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        show ((((r : ℚ).den : ℤ) : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) * ((((r : ℚ).den : ℤ) : ℚ))⁻¹ = 1
        rw [Subring.coe_intCast]; exact mul_inv_cancel₀ (by exact_mod_cast (r : ℚ).den_nz)
      · apply Subtype.ext
        show ((((r : ℚ).den : ℤ) : ℚ))⁻¹ * ((((r : ℚ).den : ℤ) : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = 1
        rw [Subring.coe_intCast]; exact inv_mul_cancel₀ (by exact_mod_cast (r : ℚ).den_nz)
    have hres_den : IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p) (((r : ℚ).den : ℤ) : ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 := by
      rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
      exact not_not.mpr hden_unit
    refine ⟨(((r : ℚ).num : ℤ) : ZMod p) * ((((r : ℚ).den : ℤ) : ZMod p))⁻¹, ?_⟩
    rw [map_mul, map_inv₀, map_intCast, map_intCast]
    have h2 := congrArg (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) hrd
    rw [map_mul, map_intCast, map_intCast] at h2
    rw [← h2, mul_inv_cancel_right₀]
    rwa [map_intCast] at hres_den
  refine ⟨e.symm.toRingHom.comp π₀, ?_⟩
  exact e.symm.surjective.comp hπ₀

theorem exists_surjective_zmod_residueField_section (p : ℕ) [Fact p.Prime] {X : Scheme.{0}}
    (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
    (ε : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)) ⟶ X) (hε : ε ≫ c = 𝟙 _)
    (s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
    (hs : IsClosed ({s} : Set (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))))) :
    ∃ π : ZMod p →+* X.residueField (ε.base s), Function.Surjective π := by
  obtain ⟨π₁, hπ₁⟩ := exists_surjective_zmod_residueField_spec_ratLocalizedAt p s hs
  obtain ⟨π₂, hπ₂⟩ := exists_surjective_residueField_of_section c ε hε s
  exact ⟨π₂.comp π₁, hπ₂.comp hπ₁⟩

end K1f
p2m_reactivate "P2MW.S_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero.K1f"

namespace K1f

theorem exists_residueField_hom_comp_eq_algebraMap_of_isAlgebraic
    (p : ℕ) {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) (P : X)
    [Algebra ℚ (X.residueField P)] [Algebra.IsAlgebraic ℚ (X.residueField P)]
    (hcompat : ∀ r : ↥(GaloisRep.ratLocalizedAt p),
      algebraMap ℚ (X.residueField P) (r : ℚ) =
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv ≫ c.appTop ≫ X.Γevaluation P) r) :
    ∃ φ : X.residueField P ⟶ CommRingCat.of (AlgebraicClosure ℚ),
      (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv ≫ c.appTop ≫ X.Γevaluation P ≫ φ =
        CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) := by
  let φ₀ : X.residueField P →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  refine ⟨CommRingCat.ofHom φ₀.toRingHom, ?_⟩
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  show φ₀ (((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv ≫ c.appTop ≫ X.Γevaluation P) r) =
    algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r
  rw [← hcompat, φ₀.commutes, IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ)]
  rfl

theorem exists_pow_mul_mem_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] (q : ℚ) :
    ∃ k : ℕ, q * (p : ℚ) ^ k ∈ GaloisRep.ratLocalizedAt p := by
  obtain ⟨k, d, hd, hdd⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.out.one_lt.ne'
  refine ⟨k, ?_⟩

  have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hdd; exact q.den_nz hdd
  have hq : q * (p : ℚ) ^ k = (q.num : ℚ) / (d : ℚ) := by
    have h1 : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
    conv_lhs => rw [h1]
    rw [hdd]; push_cast
    have hpk : ((p : ℚ)) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    field_simp
  rw [hq]
  show ((q.num : ℚ) / (d : ℚ)).den.Coprime p
  have hden : ((q.num : ℚ) / (d : ℚ)).den ∣ d := by
    have := Rat.den_dvd q.num (d : ℤ)
    rw [Rat.divInt_eq_div] at this
    push_cast at this
    exact_mod_cast this
  exact Nat.Coprime.coprime_dvd_left hden ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd).symm

theorem isLocalization_away_natCast_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] :
    IsLocalization.Away ((p : ↥(GaloisRep.ratLocalizedAt p))) ℚ := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨y, k, rfl⟩
    show IsUnit (((p : ↥(GaloisRep.ratLocalizedAt p)) ^ k : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)
    rw [Subring.coe_pow, Subring.coe_natCast]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero))
  · intro q
    obtain ⟨k, hk⟩ := exists_pow_mul_mem_ratLocalizedAt p q
    refine ⟨⟨⟨_, hk⟩, ⟨(p : ↥(GaloisRep.ratLocalizedAt p)) ^ k, k, rfl⟩⟩, ?_⟩
    show q * ((((p : ↥(GaloisRep.ratLocalizedAt p)) ^ k : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)) = q * (p : ℚ) ^ k
    rw [Subring.coe_pow, Subring.coe_natCast]
  · intro x y h
    exact ⟨1, by simpa using Subtype.ext h⟩

theorem exists_ringHom_rat_comp_eq_of_isUnit (p : ℕ) [hp : Fact p.Prime] {K : Type*} [Field K]
    (θ : ↥(GaloisRep.ratLocalizedAt p) →+* K) (hθ : IsUnit (θ (p : ↥(GaloisRep.ratLocalizedAt p)))) :
    ∃ i : ℚ →+* K, ∀ r : ↥(GaloisRep.ratLocalizedAt p), i (r : ℚ) = θ r := by
  letI := isLocalization_away_natCast_ratLocalizedAt p
  refine ⟨IsLocalization.Away.lift ((p : ↥(GaloisRep.ratLocalizedAt p))) hθ, fun r => ?_⟩
  exact IsLocalization.Away.lift_eq ((p : ↥(GaloisRep.ratLocalizedAt p))) hθ r

theorem exists_geomPoint_comp_eq_and_apply_eq_of_isUnit_of_algebraic
    (p : ℕ) [hp : Fact p.Prime] {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) (P : X)
    (hPη : IsUnit ((X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))))
    (halg : ∀ t : X.residueField P, ∃ f : Polynomial ↥(GaloisRep.ratLocalizedAt p), f ≠ 0 ∧
      Polynomial.eval₂ ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv ≫ c.appTop ≫ X.Γevaluation P).hom t f = 0) :
    ∃ xη : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X,
      xη ≫ c = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) ∧
      xη.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = P := by
  set θ : ↥(GaloisRep.ratLocalizedAt p) →+* X.residueField P :=
    ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv ≫ c.appTop ≫ X.Γevaluation P).hom with hθ

  have hθp : IsUnit (θ (p : ↥(GaloisRep.ratLocalizedAt p))) := by
    have := hPη.map (X.residue P).hom
    exact this

  obtain ⟨i, hi⟩ := exists_ringHom_rat_comp_eq_of_isUnit p θ hθp
  letI : Algebra ℚ (X.residueField P) := i.toAlgebra
  have hcompat : ∀ r : ↥(GaloisRep.ratLocalizedAt p), algebraMap ℚ (X.residueField P) (r : ℚ) = θ r := hi

  haveI : Algebra.IsAlgebraic ℚ (X.residueField P) := by
    refine ⟨fun t => ?_⟩
    obtain ⟨f, hf0, hf⟩ := halg t
    refine ⟨f.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ), ?_, ?_⟩
    · exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective ↥(GaloisRep.ratLocalizedAt p) ℚ)).mpr hf0
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      have hcomp : (algebraMap ℚ (X.residueField P)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) = θ :=
        RingHom.ext fun r => hcompat r
      rw [hcomp]; exact hf
  obtain ⟨φ, hφ⟩ := exists_residueField_hom_comp_eq_algebraMap_of_isAlgebraic p c P hcompat
  exact AlgebraicGeometry.Scheme.exists_hom_spec_comp_eq_specMap_algebraMap_and_apply_eq_of_residueField c P φ hφ

end K1f
p2m_reactivate "P2MW.S_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero.K1f"

namespace K1f

scoped instance isFractionRing_ratLocalizedAt_B7 (p : ℕ) : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ where
  map_units := by
    rintro ⟨y, hy⟩
    have : (y : ℚ) ≠ 0 := fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hy) (Subtype.ext h)
    exact isUnit_iff_ne_zero.mpr this
  surj := by
    intro q
    refine ⟨⟨⟨(q.num : ℚ), ?_⟩, ⟨⟨(q.den : ℚ), ?_⟩, ?_⟩⟩, ?_⟩
    · exact intCast_mem _ q.num
    · exact natCast_mem _ q.den
    · refine mem_nonZeroDivisors_iff_ne_zero.mpr fun h => q.den_nz ?_
      have := congrArg Subtype.val h
      simp at this
    · show q * (q.den : ℚ) = (q.num : ℚ)
      exact Rat.mul_den_eq_num q
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa using Subtype.ext h⟩

theorem span_natCast_isPrime_B7 (p : ℕ) [hp : Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)

theorem inv_intCast_mem_ratLocalizedAt_B7 (p : ℕ) [hp : Fact p.Prime] (b : ℤ) (hpb : ¬ (p : ℤ) ∣ b) :
    ((b : ℚ))⁻¹ ∈ GaloisRep.ratLocalizedAt p := by
  have hb0 : b ≠ 0 := fun h => hpb (h ▸ dvd_zero _)
  show (((b : ℚ))⁻¹).den.Coprime p
  rw [Rat.inv_intCast_den, if_neg hb0]
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr (fun h => hpb (Int.ofNat_dvd_left.mpr h)))

theorem isLocalization_atPrime_ratLocalizedAt_B7 (p : ℕ) [hp : Fact p.Prime] :
    @IsLocalization.AtPrime ℤ _ ↥(GaloisRep.ratLocalizedAt p) _ _ (Ideal.span {(p : ℤ)}) (span_natCast_isPrime_B7 p) := by
  letI := span_natCast_isPrime_B7 p
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨b, hb⟩
    have hpb : ¬ (p : ℤ) ∣ b := fun h => hb (Ideal.mem_span_singleton.mpr h)
    have hb0 : b ≠ 0 := fun h => hpb (h ▸ dvd_zero _)
    refine ⟨⟨algebraMap ℤ ↥(GaloisRep.ratLocalizedAt p) b, ⟨((b : ℚ))⁻¹, inv_intCast_mem_ratLocalizedAt_B7 p b hpb⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext; show ((b : ℚ)) * ((b : ℚ))⁻¹ = 1; exact mul_inv_cancel₀ (by exact_mod_cast hb0)
    · apply Subtype.ext; show ((b : ℚ))⁻¹ * ((b : ℚ)) = 1; exact inv_mul_cancel₀ (by exact_mod_cast hb0)
  · intro r
    have hden : ((r : ℚ).den : ℤ) ∈ (Ideal.span {(p : ℤ)}).primeCompl := by
      intro h
      replace h : ((r : ℚ).den : ℤ) ∈ Ideal.span {(p : ℤ)} := h
      rw [Ideal.mem_span_singleton, Int.natCast_dvd_natCast] at h
      have hcop : ((r : ℚ)).den.Coprime p := r.2
      exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm h)
    refine ⟨⟨(r : ℚ).num, ⟨_, hden⟩⟩, ?_⟩
    apply Subtype.ext
    show (r : ℚ) * (((r : ℚ).den : ℤ) : ℚ) = (((r : ℚ).num : ℤ) : ℚ)
    push_cast
    exact Rat.mul_den_eq_num (r : ℚ)
  · intro x y h
    exact ⟨1, by simpa using h⟩

theorem ringHom_ratLocalizedAt_ext (p : ℕ) [Fact p.Prime] {K : Type*} [Semiring K]
    (j k : ↥(GaloisRep.ratLocalizedAt p) →+* K) : j = k := by
  letI := span_natCast_isPrime_B7 p
  letI := isLocalization_atPrime_ratLocalizedAt_B7 p
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

theorem exists_polynomial_eval₂_eq_zero_of_isAlgebraic_map
    (p : ℕ) [Fact p.Prime] {K K' : Type*} [Field K] [Field K'] [Algebra ℚ K']
    (θ : ↥(GaloisRep.ratLocalizedAt p) →+* K) (ι : K →+* K') (t : K) (ht : IsAlgebraic ℚ (ι t)) :
    ∃ f : Polynomial ↥(GaloisRep.ratLocalizedAt p), f ≠ 0 ∧ Polynomial.eval₂ θ t f = 0 := by
  obtain ⟨g, hg0, hg⟩ := ht
  let f := IsLocalization.integerNormalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt p)) g
  have hf : Polynomial.eval₂ ((algebraMap ℚ K').comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) (ι t) f = 0 :=
    IsLocalization.integerNormalization_eval₂_eq_zero _ (algebraMap ℚ K') g (by rwa [Polynomial.aeval_def] at hg)

  have hmaps : (algebraMap ℚ K').comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) = ι.comp θ :=
    ringHom_ratLocalizedAt_ext p _ _
  rw [hmaps, ← Polynomial.hom_eval₂] at hf
  refine ⟨f, ?_, (map_eq_zero ι).mp hf⟩

  intro hf0
  obtain ⟨b, hb, hbg⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt p)) g
  have hbg0 : b • g = 0 := by
    rw [← hbg, show IsLocalization.integerNormalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt p)) g = 0 from hf0,
      Polynomial.map_zero]
  have hb0 : algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ↥(GaloisRep.ratLocalizedAt p) ℚ)).mpr (nonZeroDivisors.ne_zero hb)
  rw [← algebraMap_smul ℚ b g, smul_eq_zero] at hbg0
  rcases hbg0 with h | h
  · exact hb0 h
  · exact hg0 h

theorem exists_ringHom_residueField_isAlgebraic_of_isClosed
    {Y : Scheme.{0}} (b : Y ⟶ Spec (CommRingCat.of ℚ)) [LocallyOfFiniteType b] (y : Y) (hy : IsClosed ({y} : Set Y)) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra ℚ K') (ι : Y.residueField y →+* K'), ∀ u, IsAlgebraic ℚ (ι u) := by
  classical

  obtain ⟨V, hVmem, hyV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y))
    (show y ∈ (⊤ : Y.Opens) from trivial)
  have hV : IsAffineOpen V := hVmem
  set q : Spec Γ(Y, V) := hV.primeIdealOf ⟨y, hyV⟩ with hqdef
  have hq : hV.fromSpec.base q = y := hV.fromSpec_primeIdealOf ⟨y, hyV⟩

  have hqcl : IsClosed ({q} : Set (Spec Γ(Y, V))) := by
    have hpre : hV.fromSpec.base ⁻¹' {y} = {q} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        exact hV.fromSpec.isOpenEmbedding.injective (hz.trans hq.symm)
      · rintro rfl; exact hq
    rw [← hpre]
    exact hy.preimage hV.fromSpec.base.hom.continuous
  haveI hqmax : q.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hqcl

  have hφ : (b.appLE ⊤ V le_top).hom.FiniteType :=
    LocallyOfFiniteType.finiteType_appLE b (isAffineOpen_top _) hV _
  let ψ : Γ(Y, V) →+* q.asIdeal.ResidueField := algebraMap _ _
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨w, rfl⟩ := (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal).surjective z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective w
    exact ⟨a, (IsScalarTower.algebraMap_apply Γ(Y, V) (Γ(Y, V) ⧸ q.asIdeal) q.asIdeal.ResidueField a)⟩
  let τ : ℚ →+* q.asIdeal.ResidueField :=
    (ψ.comp (b.appLE ⊤ V le_top).hom).comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
  have hτ : τ.FiniteType := by
    refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℚ)).commRingCatIsoToRingEquiv.symm.surjective)
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ hψ) hφ
  letI : Algebra ℚ q.asIdeal.ResidueField := τ.toAlgebra
  haveI : Algebra.FiniteType ℚ q.asIdeal.ResidueField := hτ
  haveI : Module.Finite ℚ q.asIdeal.ResidueField := finite_of_finite_type_of_isJacobsonRing ℚ _
  haveI : Algebra.IsAlgebraic ℚ q.asIdeal.ResidueField := Algebra.IsAlgebraic.of_finite ℚ _

  let ι : Y.residueField y →+* q.asIdeal.ResidueField :=
    ((Scheme.Spec.residueFieldIso (Γ(Y, V)) q).hom.hom.comp (hV.fromSpec.residueFieldMap q).hom).comp
      (Y.residueFieldCongr hq).inv.hom
  exact ⟨q.asIdeal.ResidueField, inferInstance, inferInstance, ι, fun u => Algebra.IsAlgebraic.isAlgebraic (ι u)⟩

theorem halg_of_closedPoint
    (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
    {C : Scheme.{0}} (toBase : C ⟶ Spec (CommRingCat.of ℚ)) [SmoothOfRelativeDimension 1 toBase]
    (f₀ : C ⟶ X) (P : X) (P' : C) (hP'P : f₀.base P' = P) (hP'cl : IsClosed ({P'} : Set C)) :
    ∀ t : X.residueField P, ∃ f : Polynomial ↥(GaloisRep.ratLocalizedAt p), f ≠ 0 ∧
      Polynomial.eval₂ ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv ≫ c.appTop ≫ X.Γevaluation P).hom t f = 0 := by
  haveI := SmoothOfRelativeDimension.smooth 1 toBase
  haveI : LocallyOfFiniteType toBase := inferInstance
  obtain ⟨K', _, _, ι, hι⟩ := exists_ringHom_residueField_isAlgebraic_of_isClosed toBase P' hP'cl

  let r : X.residueField P →+* C.residueField P' := (f₀.residueFieldMap P').hom.comp (X.residueFieldCongr hP'P).inv.hom
  intro t
  exact exists_polynomial_eval₂_eq_zero_of_isAlgebraic_map p _ (ι.comp r) t (hι (r t))

end K1f
p2m_reactivate "P2MW.S_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero.K1f"

scoped instance K1f.isPreimmersion_specQ (p : ℕ) :
    IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) :=
  IsPreimmersion.of_isLocalization (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt p)) (S := ℚ)

p2m_reactivate "P2MW.S_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero.K1f"
set_option maxHeartbeats 6400000 in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c]

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (x₀ : closedPoints M₀.C)
    (y : Spec (CommRingCat.of ℚ) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
    (hx₀ : M₀.placeOfPoint x₀ = cuspInftyFull N)
    (hy : y ≫ pullback.snd c _ = 𝟙 _)
    (hyε : y ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) ≫ εinf.1)
    (hyx₀ : (y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ) = x₀.1)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)

    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g • Mη.pointEquivPlace x)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N),
        IsPlaceReductionModL A N r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))

    (s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) (hs : IsClosed ({s} : Set (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))))
    (hspec : (e₀ ≫ pullback.fst c _).base x₀.1 ⤳ εinf.1.base s)
    (P : X) (hP : P ⤳ εinf.1.base s)
    (hPη : IsUnit ((X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))))
    (hPne : P ≠ (e₀ ≫ pullback.fst c _).base x₀.1)

    (hgenP : (e₀ ≫ pullback.fst c _).base (genericPoint M₀.C) ⤳ P) :
    ∃ g : X.presheaf.stalk P, IsUnit g ∧
      ((M₀.ffEquiv.symm ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) (genericPoint M₀.C)).hom
          ((X.presheaf.stalkSpecializes hgenP).hom g)) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = (jq : LaurentSeries ℚ) := by
  classical
  haveI hdvr : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  have hpmax : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨v, hv⟩
    have hq : ((v⁻¹ : (↥(GaloisRep.ratLocalizedAt p))ˣ) : ↥(GaloisRep.ratLocalizedAt p)).1 = ((p : ℕ) : ℚ)⁻¹ := by
      have h1 : ((v : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) * (((v⁻¹ : (↥(GaloisRep.ratLocalizedAt p))ˣ) : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]; rfl
      have h2 : ((v : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = ((p : ℕ) : ℚ) := by rw [hv]; rfl
      rw [h2] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    have hden := ((v⁻¹ : (↥(GaloisRep.ratLocalizedAt p))ˣ) : ↥(GaloisRep.ratLocalizedAt p)).2
    change (((v⁻¹ : (↥(GaloisRep.ratLocalizedAt p))ˣ) : ↥(GaloisRep.ratLocalizedAt p)).1).den.Coprime p at hden
    rw [hq, Rat.inv_natCast_den, if_neg (Fact.out : p.Prime).ne_zero] at hden
    exact (Fact.out : p.Prime).ne_one ((Nat.coprime_self p).mp hden)

  have key : ∀ Q : X, IsUnit ((X.presheaf.germ ⊤ Q trivial).hom (c.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))) → ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∉ (c.base Q).asIdeal := by
    intro Q hu
    letI := StructureSheaf.stalkAlgebra ↥(GaloisRep.ratLocalizedAt p) (c.base Q)
    have e0 : algebraMap ↥(GaloisRep.ratLocalizedAt p) ((Spec.structureSheaf ↥(GaloisRep.ratLocalizedAt p)).presheaf.stalk (c.base Q)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) =
        ((Spec (.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.germ ⊤ (c.base Q) trivial).hom
          ((Scheme.ΓSpecIso (.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) := by
      show _ = ((Scheme.ΓSpecIso (.of ↥(GaloisRep.ratLocalizedAt p))).inv ≫ (Spec (.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.germ ⊤ (c.base Q) trivial).hom _
      rw [Scheme.ΓSpecIso_inv]
      erw [StructureSheaf.algebraMap_germ]
      rfl
    have e1 : (X.presheaf.germ ⊤ Q trivial).hom (c.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) =
        (c.stalkMap Q).hom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((Spec.structureSheaf ↥(GaloisRep.ratLocalizedAt p)).presheaf.stalk (c.base Q)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) := by
      rw [e0]
      erw [Scheme.Hom.germ_stalkMap_apply c ⊤ Q trivial]
      rfl
    rw [e1] at hu
    have hu2 := (isUnit_map_iff (c.stalkMap Q).hom _).mp hu
    exact (@IsLocalization.AtPrime.isUnit_to_map_iff ↥(GaloisRep.ratLocalizedAt p) _ _ _ (StructureSheaf.stalkAlgebra ↥(GaloisRep.ratLocalizedAt p) (c.base Q))
        (c.base Q).asIdeal _ (StructureSheaf.IsLocalization.to_stalk ↥(GaloisRep.ratLocalizedAt p) (c.base Q)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))).mp hu2

  have hinjRQ : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) := fun a b h => Subtype.ext h
  obtain ⟨Θ, hΘ1, hΘ2, -, -⟩ :=
    AlgebraicCurve.CurveModel.exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback hinjRQ M₀ c e₀ he₀

  have hsurj : ∀ z : M₀.C, Function.Surjective ((e₀ ≫ pullback.fst c
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).stalkMap z).hom := by
    intro z
    rw [Scheme.Hom.stalkMap_comp]
    exact (ConcreteCategory.bijective_of_isIso (e₀.stalkMap z)).2.comp
      (K1f.stalkMap_fst_genericFibre_surjective p c (e₀.base z))
  let jF : ↥(modularFunctionFieldFull N) := ⟨jq, jq_mem_full N⟩

  by_cases hPξ : P = (e₀ ≫ pullback.fst c _).base (genericPoint M₀.C)
  · subst hPξ
    obtain ⟨g0, hg0⟩ := hsurj (genericPoint M₀.C) (M₀.ffEquiv jF)
    have hjq0 : (jq : LaurentSeries ℚ) ≠ 0 := by
      intro h; have := order_jq; rw [h, HahnSeries.order_zero] at this; exact absurd this (by norm_num)
    have hjF0 : jF ≠ 0 := fun h => hjq0 (congrArg Subtype.val h)
    refine ⟨g0, ?_, ?_⟩
    · apply (isUnit_map_iff ((e₀ ≫ pullback.fst c _).stalkMap (genericPoint M₀.C)).hom g0).mp
      rw [hg0]
      exact isUnit_iff_ne_zero.mpr ((map_ne_zero M₀.ffEquiv).mpr hjF0)
    · have h2 := hΘ2 (genericPoint M₀.C) g0
      rw [hg0] at h2
      have hid : @algebraMap _ _ _ _ (AlgebraicGeometry.stalkFunctionFieldAlgebra M₀.C (genericPoint M₀.C)) (M₀.ffEquiv jF) =
          M₀.ffEquiv jF := by
        show (M₀.C.presheaf.stalkSpecializes _).hom _ = _
        rw [TopCat.Presheaf.stalkSpecializes_refl]; rfl
      erw [hid, RingEquiv.symm_apply_apply] at h2
      rw [hΘ1 _ hgenP g0, ← h2]

  obtain ⟨P', hP'P, hP'cl⟩ : ∃ P' : M₀.C, (e₀ ≫ pullback.fst c _).base P' = P ∧ IsClosed ({P'} : Set M₀.C) := by
    have hcP : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∉ (c.base P).asIdeal := key P hPη
    have hbot : (c.base P).asIdeal = ⊥ := by
      by_contra hne
      haveI := (c.base P).isPrime
      have hmax : (c.base P).asIdeal.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
      exact hcP (IsLocalRing.eq_maximalIdeal hmax ▸ hpmax)
    have hrange : P ∈ Set.range (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).base := by
      rw [Scheme.Pullback.range_fst]
      show c.base P ∈ Set.range _
      refine ⟨IsLocalRing.closedPoint ℚ, PrimeSpectrum.ext ?_⟩
      rw [hbot]
      show Ideal.comap (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) (IsLocalRing.maximalIdeal ℚ) = ⊥
      rw [show IsLocalRing.maximalIdeal ℚ = ⊥ from (IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField ℚ)), Ideal.comap_bot_of_injective _ hinjRQ]
    obtain ⟨z, hz⟩ := hrange
    refine ⟨(inv e₀).base z, ?_, ?_⟩
    · show ((inv e₀) ≫ e₀ ≫ pullback.fst c _).base z = P
      rw [IsIso.inv_hom_id_assoc]; exact hz
    · rcases (AlgebraicCurve.CurveModel.surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap ℚ M₀.toBase M₀
        (𝟙 M₀.C) (Category.id_comp _) (by rw [Scheme.Hom.stalkMap_id]; exact IsIso.id _)).2 ((inv e₀).base z) with h | h
      · exfalso; apply hPξ
        rw [← h]; show P = ((inv e₀) ≫ e₀ ≫ pullback.fst c _).base z
        rw [IsIso.inv_hom_id_assoc]; exact hz.symm
      · exact h

  have halg : ∀ t : X.residueField P, ∃ f : Polynomial ↥(GaloisRep.ratLocalizedAt p), f ≠ 0 ∧
      Polynomial.eval₂ ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv ≫ c.appTop ≫ X.Γevaluation P).hom t f = 0 :=
    K1f.halg_of_closedPoint p c M₀.toBase (e₀ ≫ pullback.fst c _) P P' hP'P hP'cl
  obtain ⟨xη, hxηc, hxηP⟩ : ∃ xη : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X,
      xη ≫ c = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) ∧
      xη.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = P :=
    K1f.exists_geomPoint_comp_eq_and_apply_eq_of_isUnit_of_algebraic p c P hPη halg

  obtain ⟨x, hx⟩ : ∃ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
      x.1 ≫ eη ≫ pullback.fst c _ = xη :=
    K1f.exists_section_comp_iso_fst_eq_of_comp_eq c _ Mη.toBase eη heη xη hxηc

  have hnu : ¬ IsUnit ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))) := by
    intro hu
    have hcs : c.base (εinf.1.base s) = s := by
      show (εinf.1 ≫ c).base s = s
      rw [εinf.2]; rfl
    letI := StructureSheaf.stalkAlgebra ↥(GaloisRep.ratLocalizedAt p) (c.base (εinf.1.base s))
    have e0 : algebraMap ↥(GaloisRep.ratLocalizedAt p) ((Spec.structureSheaf ↥(GaloisRep.ratLocalizedAt p)).presheaf.stalk (c.base (εinf.1.base s))) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) =
        ((Spec (.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.germ ⊤ (c.base (εinf.1.base s)) trivial).hom
          ((Scheme.ΓSpecIso (.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) := by
      show _ = ((Scheme.ΓSpecIso (.of ↥(GaloisRep.ratLocalizedAt p))).inv ≫ (Spec (.of ↥(GaloisRep.ratLocalizedAt p))).presheaf.germ ⊤ (c.base (εinf.1.base s)) trivial).hom _
      rw [Scheme.ΓSpecIso_inv]
      erw [StructureSheaf.algebraMap_germ]
      rfl
    have e1 : (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) =
        (c.stalkMap (εinf.1.base s)).hom
          (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((Spec.structureSheaf ↥(GaloisRep.ratLocalizedAt p)).presheaf.stalk (c.base (εinf.1.base s))) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) := by
      rw [e0]
      erw [Scheme.Hom.germ_stalkMap_apply c ⊤ (εinf.1.base s) trivial]
      rfl
    rw [e1] at hu
    have hu2 := (isUnit_map_iff (c.stalkMap (εinf.1.base s)).hom _).mp hu
    have hnotmem : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∉ (c.base (εinf.1.base s)).asIdeal :=
      (@IsLocalization.AtPrime.isUnit_to_map_iff ↥(GaloisRep.ratLocalizedAt p) _ _ _ (StructureSheaf.stalkAlgebra ↥(GaloisRep.ratLocalizedAt p) (c.base (εinf.1.base s)))
        (c.base (εinf.1.base s)).asIdeal _ (StructureSheaf.IsLocalization.to_stalk ↥(GaloisRep.ratLocalizedAt p) (c.base (εinf.1.base s)))
        ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))).mp hu2
    apply hnotmem
    rw [hcs]

    haveI hdvr : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
    have hs' : s = IsLocalRing.closedPoint ↥(GaloisRep.ratLocalizedAt p) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal s).mp hs |> IsLocalRing.eq_maximalIdeal |> fun h =>
        PrimeSpectrum.ext h
    rw [hs']
    show ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨v, hv⟩
    have hq : ((v⁻¹ : (↥(GaloisRep.ratLocalizedAt p))ˣ) : ↥(GaloisRep.ratLocalizedAt p)).1 = ((p : ℕ) : ℚ)⁻¹ := by
      have h1 : ((v : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) * (((v⁻¹ : (↥(GaloisRep.ratLocalizedAt p))ˣ) : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]; rfl
      have h2 : ((v : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = ((p : ℕ) : ℚ) := by rw [hv]; rfl
      rw [h2] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    have hden := ((v⁻¹ : (↥(GaloisRep.ratLocalizedAt p))ˣ) : ↥(GaloisRep.ratLocalizedAt p)).2
    change (((v⁻¹ : (↥(GaloisRep.ratLocalizedAt p))ˣ) : ↥(GaloisRep.ratLocalizedAt p)).1).den.Coprime p at hden
    rw [hq, Rat.inv_natCast_den, if_neg (Fact.out : p.Prime).ne_zero] at hden
    exact (Fact.out : p.Prime).ne_one ((Nat.coprime_self p).mp hden)

  obtain ⟨A, hA, xA, hxAη, hxAs⟩ :=
    ModularCurve.exists_liesOverPrime_schemeHomOver_comp_eq_base_closedPoint_eq_of_specializes p c ρ hρ xη hxηc
      (εinf.1.base s) (by rw [hxηP]; exact hP) hnu

  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA

  obtain ⟨yb, hyb⟩ : ∃ yb : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C // q ≫ (Ms A hA).toBase = 𝟙 _},
      yb.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 :=
    K1f.exists_section_comp_iso_fst_eq_of_comp_eq' c _ (Ms A hA).toBase (es A hA) (hes_iso A hA) (hes A hA) _ (by
      rw [Category.assoc, xA.2, K1f.specMap_ofHom_comp_specMap_ofHom])
  obtain ⟨r, hr, hred⟩ := hsp A hA
  have h1 : (Ms A hA).pointEquivPlace yb = r (Mη.pointEquivPlace x) := hred xA x yb (by rw [hx, hxAη]) hyb

  let xAinf : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c :=
    ⟨Spec.map (CommRingCat.ofHom (ρ A hA)) ≫ εinf.1, by rw [Category.assoc, εinf.2, Category.comp_id]⟩
  obtain ⟨xinf, hxinf⟩ : ∃ xinf : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
      xinf.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xAinf.1 :=
    K1f.exists_section_comp_iso_fst_eq_of_comp_eq c _ Mη.toBase eη heη _ (by
      rw [Category.assoc, xAinf.2, K1f.specMap_ofHom_comp_specMap_ofHom, hρ A hA])

  let yinf : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ y
  have hSpecR : Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hyinf1 : yinf ≫ pullback.fst c _ = xinf.1 ≫ eη ≫ pullback.fst c _ := by
    rw [hxinf]
    show (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ y) ≫ pullback.fst c _ =
      Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (ρ A hA)) ≫ εinf.1
    rw [Category.assoc, hyε, ← Category.assoc, hSpecR, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  have hclosedQ : ∀ z : Spec (CommRingCat.of (AlgebraicClosure ℚ)), (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))).base z =
      IsLocalRing.closedPoint ℚ := fun z => Subsingleton.elim _ _
  have hyinf2 : (yinf ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 := by
    show (inv e₀).base (y.base ((Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))).base _)) = x₀.1
    rw [hclosedQ]
    exact hyx₀
  have hcomapinf := hcompat xinf yinf x₀ hyinf1 hyinf2
  have hxinfpl : Mη.pointEquivPlace xinf = cuspInftyBar N := by
    apply ModularCurve.eq_cuspInftyBar_of_comap_toSubring_eq_cuspInftyFull
    rw [hcomapinf, hx₀]

  obtain ⟨ybinf, hybinf⟩ : ∃ yb' : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C // q ≫ (Ms A hA).toBase = 𝟙 _},
      yb'.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xAinf.1 :=
    K1f.exists_section_comp_iso_fst_eq_of_comp_eq' c _ (Ms A hA).toBase (es A hA) (hes_iso A hA) (hes A hA) _ (by
      rw [Category.assoc, xAinf.2, K1f.specMap_ofHom_comp_specMap_ofHom])
  have h2 : (Ms A hA).pointEquivPlace ybinf = r (cuspInftyBar N) := by
    rw [← hxinfpl]; exact hred xAinf xinf ybinf hxinf hybinf

  have hyy : yb = ybinf := by
    obtain ⟨π, hπ⟩ := K1f.exists_surjective_zmod_residueField_section p c εinf.1 εinf.2 s hs

    have hres : (Spec.map (CommRingCat.ofHom (residue ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A)) =
        IsLocalRing.closedPoint ↥A := by
      apply PrimeSpectrum.ext
      show Ideal.comap (residue ↥A) (IsLocalRing.closedPoint (ResidueField ↥A)).asIdeal = IsLocalRing.maximalIdeal ↥A
      rw [show (IsLocalRing.closedPoint (ResidueField ↥A)).asIdeal = ⊥ from
        (IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField _)), ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
    have hs' : s = IsLocalRing.closedPoint ↥(GaloisRep.ratLocalizedAt p) :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal s).mp hs))

    have hρs : (Spec.map (CommRingCat.ofHom (ρ A hA))).base (IsLocalRing.closedPoint ↥A) = s := by
      rw [hs']
      apply PrimeSpectrum.ext
      show Ideal.comap (ρ A hA) (IsLocalRing.maximalIdeal ↥A) = IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p)
      haveI : (Ideal.comap (ρ A hA) (IsLocalRing.maximalIdeal ↥A)).IsPrime := Ideal.comap_isPrime _ _
      have hpmem : ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ Ideal.comap (ρ A hA) (IsLocalRing.maximalIdeal ↥A) := by
        rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
        have : ((ρ A hA ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) : ↥A) : (AlgebraicClosure ℚ)) = ((p : ℕ) : (AlgebraicClosure ℚ)) := by
          have := RingHom.congr_fun (hρ A hA) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))
          simpa using this
        rw [this]
        exact hA
      have hne : Ideal.comap (ρ A hA) (IsLocalRing.maximalIdeal ↥A) ≠ ⊥ := fun h => by
        rw [h] at hpmem
        exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast (Subtype.ext_iff.mp hpmem : ((p : ℕ) : ℚ) = 0))
      exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)
    have h1 : (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1).base (IsLocalRing.closedPoint (ResidueField ↥A)) =
        εinf.1.base s := by
      show xA.1.base ((Spec.map (CommRingCat.ofHom (residue ↥A))).base _) = _
      rw [hres, hxAs]
    have h2 : (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xAinf.1).base (IsLocalRing.closedPoint (ResidueField ↥A)) =
        εinf.1.base s := by
      show εinf.1.base ((Spec.map (CommRingCat.ofHom (ρ A hA))).base ((Spec.map (CommRingCat.ofHom (residue ↥A))).base _)) = _
      rw [hres, hρs]
    have heq := AlgebraicGeometry.Scheme.hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField (εinf.1.base s) p π hπ _ _ h1 h2

    haveI := hes_iso A hA
    apply Subtype.ext
    apply (cancel_mono (es A hA)).mp
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hyb, hybinf, heq]
    · rw [Category.assoc, Category.assoc, hes A hA, yb.2, ybinf.2]
  have h3 : r (Mη.pointEquivPlace x) = r (cuspInftyBar N) := by rw [← h1, ← h2, hyy]

  obtain ⟨Pinf, hPinf⟩ : ∃ Pinf : Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N),
      ∀ f : modularFunctionFieldFullC (ResidueField ↥A) N,
        f ∈ Pinf.toValuationSubring ↔ 0 ≤ ((f : modularFunctionFieldFullC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)).order :=
    ⟨ModularCurve.qInftyPlaceMod (ResidueField ↥A) (jqModC_mem_full (ResidueField ↥A) N), fun f => Iff.rfl⟩
  obtain ⟨hrinf, huniq⟩ :=
    ModularCurve.IsPlaceReductionModL.apply_cuspInftyBar_eq_and_eq_cuspInftyBar_of_apply_eq_of_ord_ne_zero N p hpN A hA r hr Pinf hPinf

  have hP'mem : P' ∈ closedPoints M₀.C := hP'cl
  let yP : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) :=
    pullback.lift xη (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) (by rw [hxηc, hSpecR])
  have hyP1 : yP ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ := by rw [pullback.lift_fst, hx]
  have hinj : Function.Injective (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (pullback.fst c _).isEmbedding.injective.comp e₀.homeomorph.injective
  have hyP2 : (yP ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = P' := by
    apply hinj
    rw [hP'P]
    show ((yP ≫ inv e₀) ≫ e₀ ≫ pullback.fst c _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = P
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst, hxηP]
  have hcomapP := hcompat x yP ⟨P', hP'mem⟩ hyP1 hyP2

  have hw_ne : Mη.pointEquivPlace x ≠ cuspInftyBar N := by
    intro hw
    have hsub : (M₀.placeOfPoint ⟨P', hP'mem⟩).toValuationSubring.toSubring =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring := by
      rw [← hcomapP, hw, ← hxinfpl, hcomapinf]
    have heq : (⟨P', hP'mem⟩ : closedPoints M₀.C) = x₀ :=
      M₀.placeOfPoint_bijective.1 (Place.ext (ValuationSubring.toSubring_injective hsub))
    apply hPne
    rw [← hP'P, ← heq]
  have hord : (Mη.pointEquivPlace x).ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) = 0 := by
    by_contra h
    exact hw_ne (huniq _ (h3.trans hrinf) h)

  obtain ⟨g', hg'unit, hg'read⟩ : ∃ g' : M₀.C.presheaf.stalk P', IsUnit g' ∧
      ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk P') M₀.C.functionField g') : ↥(modularFunctionFieldFull N)) :
        LaurentSeries ℚ) = (jq : LaurentSeries ℚ) := by
    set w := Mη.pointEquivPlace x with hwdef
    set jB : ↥(modularFunctionFieldBar N) := ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ with hjB
    let jF : ↥(modularFunctionFieldFull N) := ⟨jq, jq_mem_full N⟩
    have hjq0 : (jq : LaurentSeries ℚ) ≠ 0 := by
      intro h; have := order_jq; rw [h, HahnSeries.order_zero] at this; exact absurd this (by norm_num)
    have hjF0 : jF ≠ 0 := fun h => hjq0 (congrArg Subtype.val h)
    have hjB0 : jB ≠ 0 := by
      intro h0
      have h1 : (jB : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [h0]; rfl
      exact (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr hjq0 h1

    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hjB0 hπ
    rw [hord, zpow_zero, mul_one] at hu
    have hmemB : jB ∈ w.toValuationSubring := by rw [hu]; exact (u : w.toValuationSubring).2
    have hinvB : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : ↥(modularFunctionFieldBar N)) = jB⁻¹ := by
      rw [hu]
      symm
      apply inv_eq_of_mul_eq_one_right
      rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
    have hmemBinv : jB⁻¹ ∈ w.toValuationSubring := by rw [← hinvB]; exact ((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring).2

    let φ : ↥(modularFunctionFieldFull N) →+* ↥(modularFunctionFieldBar N) :=
      (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := (AlgebraicClosure ℚ)) (B := ↥(modularFunctionFieldFull N))).toRingHom
    have hφj : φ jF = jB := by
      show baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N) ((1 : (AlgebraicClosure ℚ)) ⊗ₜ[ℚ] jF) = jB
      rw [baseChangeEquiv_one_tmul]
    have hjF : jF ∈ (M₀.placeOfPoint ⟨P', hP'mem⟩).toValuationSubring.toSubring := by
      rw [← hcomapP]; show φ jF ∈ w.toValuationSubring.toSubring; rw [hφj]; exact hmemB
    have hjFinv : jF⁻¹ ∈ (M₀.placeOfPoint ⟨P', hP'mem⟩).toValuationSubring.toSubring := by
      rw [← hcomapP]; show φ jF⁻¹ ∈ w.toValuationSubring.toSubring; rw [map_inv₀, hφj]; exact hmemBinv

    have hrange := M₀.range_stalk_eq ⟨P', hP'mem⟩
    rw [← hrange] at hjF hjFinv
    obtain ⟨g', hg'⟩ := hjF
    obtain ⟨h', hh'⟩ := hjFinv
    refine ⟨g', ?_, ?_⟩
    · have hprod : (M₀.ffEquiv.symm : M₀.C.functionField ≃+* ↥(modularFunctionFieldFull N)).toRingHom.comp
          (algebraMap (M₀.C.presheaf.stalk P') M₀.C.functionField) (g' * h') = 1 := by
        rw [map_mul]; erw [hg', hh']; exact mul_inv_cancel₀ hjF0
      have h1 : algebraMap (M₀.C.presheaf.stalk P') M₀.C.functionField (g' * h') = 1 := by
        have := congrArg M₀.ffEquiv hprod
        simpa using this
      exact IsUnit.of_mul_eq_one h' ((IsFractionRing.injective (M₀.C.presheaf.stalk P') M₀.C.functionField) (by rw [h1, map_one]))
    · have := congrArg (fun z : ↥(modularFunctionFieldFull N) => (z : LaurentSeries ℚ)) hg'
      exact this

  subst hP'P
  obtain ⟨g0, hg0⟩ := hsurj P' g'
  refine ⟨g0, ?_, ?_⟩
  · exact (isUnit_map_iff ((e₀ ≫ pullback.fst c _).stalkMap P').hom g0).mp (hg0 ▸ hg'unit)
  · have h2 := hΘ2 P' g0
    rw [hg0] at h2
    rw [hΘ1 _ hgenP g0, ← h2]
    exact hg'read

end S_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_isUnit_stalk_ffEquiv_symm_stalkMap_genericPoint_eq_jq_of_specializes_cuspSection_of_ratCurveModel_compat_of_neZero (solution)
