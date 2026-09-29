-- Prove2me | solution 1 for M4aHerbrand.idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/715568a1-d946-567c-a7a8-407300eed99c

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq
import Theorems.Thm_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"
set_option autoImplicit false
set_option maxSynthPendingDepth 3
p2m_open "NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq.M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart idelesTrivialOn principalIdeles AdeleBaseChange AdeleBaseChange.mem_range_idelicNorm_of_forall_exists_norm_eq restrictNormalHom_idelicArtinMap_eq"
namespace LocNormProof
p2m_open "M4aHerbrand"
open IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise

@[elab_as_elim]
private theorem adicCompletion_induction_on {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {u : IsDedekindDomain.HeightOneSpectrum R}
    {p : u.adicCompletion K → Prop} (x : u.adicCompletion K) (hp : IsClosed {x | p x})
    (ih : ∀ k : WithVal (u.valuation K), p k) : p x := by
  obtain ⟨y, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K u x
  exact UniformSpace.Completion.induction_on
    (p := fun y => p (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y)) y
    (hp.preimage (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K u)) ih

section tower
variable (E L F : Type*) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F]

theorem adicCompletionSemialgHom_tower
    (v : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 L)) (hu : u.under (𝓞 E) = v)
    (w : HeightOneSpectrum (𝓞 F)) (hwu : w.under (𝓞 L) = u) (hw : w.under (𝓞 E) = v) (z : v.adicCompletion E) :
    Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) z =
      Extension.adicCompletionSemialgHom L F (⟨w, hwu⟩ : u.Extension (𝓞 F))
        (Extension.adicCompletionSemialgHom E L (⟨u, hu⟩ : v.Extension (𝓞 L)) z) := by
  induction z using adicCompletion_induction_on with
  | hp =>
    exact isClosed_eq (Extension.adicCompletionSemialgHom_continuous E F _)
      ((Extension.adicCompletionSemialgHom_continuous L F _).comp (Extension.adicCompletionSemialgHom_continuous E L _))
  | ih x =>
    rw [Extension.adicCompletionSemialgHom_coe, Extension.adicCompletionSemialgHom_coe, Extension.adicCompletionSemialgHom_coe]
    congr 1
    simp [← IsScalarTower.algebraMap_apply]
end tower

section action
variable (E L F : Type*) [Field E] [Field L] [Field F] [NumberField F] [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F]

omit [NumberField F] in
theorem restrictScalars_smul_valuationSubring (σ : F ≃ₐ[L] F) (S : ValuationSubring F) :
    (σ.restrictScalars E) • S = σ • S := by
  ext x
  simp only [ValuationSubring.mem_smul_pointwise_iff_exists]
  rfl

theorem mem_decomp_iff_restrictScalars_mem (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[L] F) :
    σ ∈ NumberField.PlaceDecomp.decomp L F w ↔ σ.restrictScalars E ∈ NumberField.PlaceDecomp.decomp E F w := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, restrictScalars_smul_valuationSubring]

theorem smul_eq_restrictScalars_smul (w : HeightOneSpectrum (𝓞 F)) (σ : NumberField.PlaceDecomp.decomp L F w)
    (z : w.adicCompletion F) :
    σ • z = (⟨(σ : F ≃ₐ[L] F).restrictScalars E, (mem_decomp_iff_restrictScalars_mem E L F w σ).mp σ.2⟩ :
      NumberField.PlaceDecomp.decomp E F w) • z := by
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def]
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  rw [NumberField.PlaceDecomp.actRingEquiv_apply, NumberField.PlaceDecomp.actRingEquiv_apply]
  rfl
end action

section core
variable (D M : Type*) [Group D] [Finite D] [Field M] [MulSemiringAction D M] [FaithfulSMul D M]

noncomputable abbrev galSub (H' : Subgroup D) : Subgroup (M ≃ₐ[FixedPoints.subfield D M] M) :=
  H'.map (FixedPoints.toAlgAutMulEquiv D M).toMonoidHom

noncomputable abbrev fixFld (H' : Subgroup D) : IntermediateField (FixedPoints.subfield D M) M :=
  IntermediateField.fixedField (galSub D M H')

theorem toAlgAutMulEquiv_apply (g : D) (x : M) : FixedPoints.toAlgAutMulEquiv D M g x = g • x := rfl

theorem mem_fixFld_iff (H' : Subgroup D) (x : M) : x ∈ fixFld D M H' ↔ ∀ h ∈ H', h • x = x := by
  simp only [IntermediateField.mem_fixedField_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, toAlgAutMulEquiv_apply]

theorem isMulCommutative_gal [IsMulCommutative D] : IsMulCommutative (M ≃ₐ[FixedPoints.subfield D M] M) :=
  ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := (FixedPoints.toAlgAutMulEquiv D M).surjective a
    obtain ⟨b, rfl⟩ := (FixedPoints.toAlgAutMulEquiv D M).surjective b
    rw [← map_mul, ← map_mul, mul_comm]⟩⟩

scoped instance galSub_normal [IsMulCommutative D] (H' : Subgroup D) : (galSub D M H').Normal :=
  haveI := isMulCommutative_gal D M
  inferInstance

theorem algebraMap_norm_fixFld [IsMulCommutative D] (H' : Subgroup D) (x : fixFld D M H') :
    algebraMap (FixedPoints.subfield D M) M (Algebra.norm (FixedPoints.subfield D M) x) =
      ∏ᶠ c : D ⧸ H', Quotient.out c • (x : M) := by
  classical
  haveI := Fintype.ofFinite D

  have h1 := Algebra.norm_eq_prod_automorphisms (FixedPoints.subfield D M) x
  apply_fun algebraMap (fixFld D M H') M at h1
  rw [← IsScalarTower.algebraMap_apply, map_prod] at h1
  rw [h1, finprod_eq_prod_of_fintype]

  let e : D ≃* (M ≃ₐ[FixedPoints.subfield D M] M) := FixedPoints.toAlgAutMulEquiv D M
  let eq : D ⧸ H' ≃* (M ≃ₐ[FixedPoints.subfield D M] M) ⧸ galSub D M H' := QuotientGroup.congr H' (galSub D M H') e rfl
  let nq := IsGalois.normalAutEquivQuotient (galSub D M H')
  symm
  refine Fintype.prod_equiv (eq.toEquiv.trans nq.toEquiv) _ _ fun c => ?_

  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H' d
  have hx : (h : D) • (x : M) = x := (mem_fixFld_iff D M H' x).mp x.2 h h.2
  rw [hh, mul_smul, hx]
  show d • (x : M) = ((nq (eq (QuotientGroup.mk d))) x : M)
  have : eq (QuotientGroup.mk d) = QuotientGroup.mk (e d) := rfl
  rw [this, IsGalois.normalAutEquivQuotient_apply]
  show d • (x : M) = algebraMap (fixFld D M H') M (((e d).restrictNormal (fixFld D M H')) x)
  rw [AlgEquiv.restrictNormal_commutes]
  rfl

end core

section local_
variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)] (w : HeightOneSpectrum (𝓞 F))

scoped instance isMulCommutative_decomp : IsMulCommutative ↥(NumberField.PlaceDecomp.decomp E F w) :=
  ⟨⟨fun a b => Subtype.ext (mul_comm (a : F ≃ₐ[E] F) (b : F ≃ₐ[E] F))⟩⟩

scoped instance faithfulSMul_decomp' : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F) :=
  NumberField.PlaceDecomp.faithfulSMul_decomp E F w

omit [NumberField E] [IsGalois E F] [IsMulCommutative (F ≃ₐ[E] F)] in

theorem forall_decomp_smul_iff (L : IntermediateField E F) (H' : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w))
    (hLH : L.fixingSubgroup = H'.map (NumberField.PlaceDecomp.decomp E F w).subtype) (y : w.adicCompletion F) :
    (∀ σ : NumberField.PlaceDecomp.decomp (↥L) F w, σ • y = y) ↔ ∀ h ∈ H', h • y = y := by
  constructor
  · intro hy h hh
    have hmem : (h : F ≃ₐ[E] F) ∈ L.fixingSubgroup := hLH ▸ Subgroup.mem_map_of_mem _ hh
    let σ : F ≃ₐ[↥L] F := IntermediateField.fixingSubgroupEquiv L ⟨h, hmem⟩
    have hσ : σ.restrictScalars E = (h : F ≃ₐ[E] F) := rfl
    have hσd : σ ∈ NumberField.PlaceDecomp.decomp (↥L) F w :=
      (mem_decomp_iff_restrictScalars_mem E (↥L) F w σ).mpr (hσ ▸ h.2)
    have key := hy ⟨σ, hσd⟩
    rw [smul_eq_restrictScalars_smul E (↥L) F w] at key
    have heq : (⟨(σ : F ≃ₐ[↥L] F).restrictScalars E, (mem_decomp_iff_restrictScalars_mem E (↥L) F w σ).mp hσd⟩ :
        NumberField.PlaceDecomp.decomp E F w) = h := Subtype.ext hσ
    rwa [heq] at key
  · intro hy σ
    rw [smul_eq_restrictScalars_smul E (↥L) F w]
    have h1 : (σ : F ≃ₐ[↥L] F).restrictScalars E ∈ L.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (σ : F ≃ₐ[↥L] F).commutes ⟨x, hx⟩
    rw [hLH] at h1
    obtain ⟨h, hh, hh'⟩ := Subgroup.mem_map.mp h1
    have heq : (⟨(σ : F ≃ₐ[↥L] F).restrictScalars E, (mem_decomp_iff_restrictScalars_mem E (↥L) F w σ).mp σ.2⟩ :
        NumberField.PlaceDecomp.decomp E F w) = h := Subtype.ext hh'.symm
    rw [heq]
    exact hy h hh

omit [IsMulCommutative (F ≃ₐ[E] F)] in

theorem mem_fixedPoints_iff_mem_range (y : w.adicCompletion F) :
    y ∈ FixedPoints.subfield ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F) ↔
      y ∈ Set.range (Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F))) :=
  NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom E F w y

noncomputable def baseEquiv :
    (w.under (𝓞 E)).adicCompletion E ≃+* ↥(FixedPoints.subfield ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)) :=
  RingEquiv.ofBijective
    (((Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F))) :
        (w.under (𝓞 E)).adicCompletion E →+* w.adicCompletion F).codRestrict
      (FixedPoints.subfield ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F))
      (fun z => (mem_fixedPoints_iff_mem_range E F w _).mpr ⟨z, rfl⟩))
    ⟨fun z₁ z₂ h => ((Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F))) :
        (w.under (𝓞 E)).adicCompletion E →+* w.adicCompletion F).injective (congrArg Subtype.val h),
     fun y => by
      obtain ⟨z, hz⟩ := (mem_fixedPoints_iff_mem_range E F w y).mp y.2
      exact ⟨z, Subtype.ext hz⟩⟩

omit [IsMulCommutative (F ≃ₐ[E] F)] in
theorem coe_baseEquiv (z : (w.under (𝓞 E)).adicCompletion E) :
    (baseEquiv E F w z : w.adicCompletion F) = Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F)) z :=
  rfl

variable (L : IntermediateField E F) (H' : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w))
  (hLH : L.fixingSubgroup = H'.map (NumberField.PlaceDecomp.decomp E F w).subtype)

omit [IsMulCommutative (F ≃ₐ[E] F)] in

theorem range_adicCompletionSemialgHom_eq (u : HeightOneSpectrum (𝓞 ↥L)) (hu : w.under (𝓞 ↥L) = u) :
    Set.range (Extension.adicCompletionSemialgHom (↥L) F (⟨w, hu⟩ : u.Extension (𝓞 F))) =
      {y | ∀ σ : NumberField.PlaceDecomp.decomp (↥L) F w, σ • y = y} := by
  subst hu
  ext y
  exact (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom (↥L) F w y).symm

variable (wL : (w.under (𝓞 E)).Extension (𝓞 ↥L)) (hwL : w.under (𝓞 ↥L) = wL.1)

omit [IsMulCommutative (F ≃ₐ[E] F)] in
include hLH in
theorem mem_fixFld_iff_mem_range (y : w.adicCompletion F) :
    y ∈ fixFld ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F) H' ↔
      y ∈ Set.range (Extension.adicCompletionSemialgHom (↥L) F (⟨w, hwL⟩ : (wL.1).Extension (𝓞 F))) := by
  rw [mem_fixFld_iff, ← forall_decomp_smul_iff E F w L H' hLH, range_adicCompletionSemialgHom_eq E F w L wL.1 hwL]
  rfl

noncomputable def layerEquiv :
    wL.1.adicCompletion ↥L ≃+* ↥(fixFld ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F) H') :=
  RingEquiv.ofBijective
    (((Extension.adicCompletionSemialgHom (↥L) F (⟨w, hwL⟩ : (wL.1).Extension (𝓞 F))) :
        wL.1.adicCompletion ↥L →+* w.adicCompletion F).codRestrict
      (fixFld ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F) H')
      (fun z => (mem_fixFld_iff_mem_range E F w L H' hLH wL hwL _).mpr ⟨z, rfl⟩))
    ⟨fun z₁ z₂ h => ((Extension.adicCompletionSemialgHom (↥L) F (⟨w, hwL⟩ : (wL.1).Extension (𝓞 F))) :
        wL.1.adicCompletion ↥L →+* w.adicCompletion F).injective (congrArg Subtype.val h),
     fun y => by
      obtain ⟨z, hz⟩ := (mem_fixFld_iff_mem_range E F w L H' hLH wL hwL y).mp y.2
      exact ⟨z, Subtype.ext hz⟩⟩

omit [IsMulCommutative (F ≃ₐ[E] F)] in
theorem coe_layerEquiv (z : wL.1.adicCompletion ↥L) :
    (layerEquiv E F w L H' hLH wL hwL z : w.adicCompletion F) =
      Extension.adicCompletionSemialgHom (↥L) F (⟨w, hwL⟩ : (wL.1).Extension (𝓞 F)) z :=
  rfl

include hLH hwL in

theorem exists_norm_eq (a : (w.under (𝓞 E)).adicCompletion E) (b : w.adicCompletion F) (hb : ∀ h ∈ H', h • b = b)
    (hN : ∏ᶠ c : ↥(NumberField.PlaceDecomp.decomp E F w) ⧸ H', Quotient.out c • b =
      Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F)) a) :
    ∃ y : wL.1.adicCompletion ↥L, Algebra.norm ((w.under (𝓞 E)).adicCompletion E) y = a := by
  have hbmem : b ∈ fixFld ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F) H' :=
    (mem_fixFld_iff _ _ H' b).mpr hb
  refine ⟨(layerEquiv E F w L H' hLH wL hwL).symm ⟨b, hbmem⟩, ?_⟩
  have he : (algebraMap ↥(FixedPoints.subfield ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F))
        ↥(fixFld ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F) H')).comp
        (baseEquiv E F w : (w.under (𝓞 E)).adicCompletion E →+* _) =
      ((layerEquiv E F w L H' hLH wL hwL : wL.1.adicCompletion ↥L →+* _)).comp
        (algebraMap ((w.under (𝓞 E)).adicCompletion E) (wL.1.adicCompletion ↥L)) := by
    ext z
    show (baseEquiv E F w z : w.adicCompletion F) = (layerEquiv E F w L H' hLH wL hwL (algebraMap _ _ z) : w.adicCompletion F)
    rw [coe_baseEquiv, coe_layerEquiv]
    exact adicCompletionSemialgHom_tower E (↥L) F (w.under (𝓞 E)) wL.1 wL.2 w hwL rfl z
  rw [Algebra.norm_eq_of_equiv_equiv (baseEquiv E F w) (layerEquiv E F w L H' hLH wL hwL) he, RingEquiv.apply_symm_apply]
  apply (baseEquiv E F w).injective
  rw [RingEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_baseEquiv]
  show algebraMap ↥(FixedPoints.subfield ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)) (w.adicCompletion F)
      (Algebra.norm ↥(FixedPoints.subfield ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F))
        (⟨b, hbmem⟩ : ↥(fixFld ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F) H'))) = _
  rw [algebraMap_norm_fixFld, ← hN]

end local_

section global

theorem nonempty_extension (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (v : HeightOneSpectrum (𝓞 E)) : Nonempty (v.Extension (𝓞 F)) := by
  haveI := v.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) v.asIdeal
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hP.over, Ideal.under_def]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨⟨P, hPm.isPrime, hP0⟩, HeightOneSpectrum.ext hP.over.symm⟩⟩

theorem restrictNormalHom_eq_one_of_mem_range_idelicNorm
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (L : Type) [Field L] [NumberField L] [Algebra E L] [Algebra L F] [IsScalarTower E L F] [IsGalois E L]
    [IsMulCommutative (L ≃ₐ[E] L)]
    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (x : (AdeleRing (𝓞 E) E)ˣ) (hxN : x ∈ (genuineBaseChange E L).idelicNorm.range) :
    AlgEquiv.restrictNormalHom L (r x) = 1 := by

  obtain ⟨𝔯, h𝔯, hram⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd E L
  obtain ⟨𝔣L, -, -, hadmL⟩ :=
    LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E L 𝔯 h𝔯 hram (Module.finrank E L)

  obtain ⟨rL, hrL₁, hrL₂, hrL₃, hrL₄⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank E L 𝔣L hadmL

  rw [M4aHerbrand.restrictNormalHom_idelicArtinMap_eq E F L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ 𝔣L hadmL rL hrL₁ hrL₂ hrL₃ hrL₄ x]
  have hker : x ∈ rL.ker := by rw [hrL₂]; exact Subgroup.mem_sup_right hxN
  exact hker
end global

end M4aHerbrand.LocNormProof
p2m_reactivate "P2MW.S_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq.M4aHerbrand P2MW.S_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq.M4aHerbrand.LocNormProof"
p2m_reactivate "P2MW.S_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq.M4aHerbrand"

open M4aHerbrand.LocNormProof in

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (v : HeightOneSpectrum (𝓞 E)) (a : (v.adicCompletion E)ˣ) (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) (hxv : finPart v x = a)

    (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (H' : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w))
    (b : (w.adicCompletion F)ˣ) (hb : ∀ h ∈ H', h • b = b)
    (hN : (((∏ᶠ c : ↥(NumberField.PlaceDecomp.decomp E F w) ⧸ H', (Quotient.out c) • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
        w.adicCompletion F) =
      IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) (a : v.adicCompletion E)) :
    r x ∈ H'.map (NumberField.PlaceDecomp.decomp E F w).subtype := by
  classical
  subst hw

  set H'' : Subgroup (F ≃ₐ[E] F) := H'.map (NumberField.PlaceDecomp.decomp E F w).subtype with hH''
  haveI hLcomm : IsMulCommutative (↥(IntermediateField.fixedField H'') ≃ₐ[E] ↥(IntermediateField.fixedField H'')) :=
    ⟨⟨fun s t => by
      obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := ↥(IntermediateField.fixedField H'')) F s
      obtain ⟨t, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := ↥(IntermediateField.fixedField H'')) F t
      rw [← map_mul, ← map_mul, mul_comm]⟩⟩
  have hLH : (IntermediateField.fixedField H'').fixingSubgroup = H'.map (NumberField.PlaceDecomp.decomp E F w).subtype :=
    IntermediateField.fixingSubgroup_fixedField H''
  have hLE : (w.under (𝓞 ↥(IntermediateField.fixedField H''))).under (𝓞 E) = w.under (𝓞 E) := by
    ext1
    simp [HeightOneSpectrum.under_asIdeal, Ideal.under_under]

  have hx_inf : ((x : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).1 = 1 := congrArg Units.val hx.1
  have hx_off : ∀ v' : HeightOneSpectrum (𝓞 E), v' ≠ w.under (𝓞 E) →
      (((x : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v' = 1 :=
    fun v' hv' => congrArg Units.val (hx.2 v' (Set.mem_compl_singleton_iff.mpr hv'))
  have hx_at : (((x : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) (w.under (𝓞 E)) =
      (a : (w.under (𝓞 E)).adicCompletion E) :=
    congrArg Units.val hxv

  have hb' : ∀ h ∈ H', h • (b : w.adicCompletion F) = b := fun h hh => congrArg Units.val (hb h hh)
  have hN' : ∏ᶠ c : ↥(NumberField.PlaceDecomp.decomp E F w) ⧸ H', Quotient.out c • (b : w.adicCompletion F) =
      IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F
        (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F)) (a : (w.under (𝓞 E)).adicCompletion E) := by
    rw [← hN]
    change _ = Units.coeHom (w.adicCompletion F) (∏ᶠ c : ↥(NumberField.PlaceDecomp.decomp E F w) ⧸ H', Quotient.out c • b)
    rw [MonoidHom.map_finprod _ (Set.toFinite _)]
    rfl

  have wall : ∃ (wL : (w.under (𝓞 E)).Extension (𝓞 ↥(IntermediateField.fixedField H'')))
      (y : wL.1.adicCompletion ↥(IntermediateField.fixedField H'')),
      Algebra.norm ((w.under (𝓞 E)).adicCompletion E) y = (a : (w.under (𝓞 E)).adicCompletion E) :=
    ⟨⟨w.under (𝓞 ↥(IntermediateField.fixedField H'')), hLE⟩,
      exists_norm_eq E F w (IntermediateField.fixedField H'') H' hLH ⟨w.under (𝓞 ↥(IntermediateField.fixedField H'')), hLE⟩ rfl
        (a : (w.under (𝓞 E)).adicCompletion E) (b : w.adicCompletion F) hb' hN'⟩

  have hxN : x ∈ (genuineBaseChange E ↥(IntermediateField.fixedField H'')).idelicNorm.range := by
    refine M4aHerbrand.AdeleBaseChange.mem_range_idelicNorm_of_forall_exists_norm_eq E _ (genuineBaseChange E _) x
      (fun v' => ?_) (fun v' hv' _ => ?_)
    · by_cases hv' : v' = w.under (𝓞 E)
      · subst hv'
        obtain ⟨wL, y, hy⟩ := wall
        exact ⟨wL, y, hy.trans hx_at.symm⟩
      · obtain ⟨wL⟩ := nonempty_extension E (↥(IntermediateField.fixedField H'')) v'
        exact ⟨wL, 1, by rw [map_one, hx_off v' hv']⟩
    · rw [hx_inf]
      show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv' 1
      rw [map_one]; exact one_pos

  have hres := restrictNormalHom_eq_one_of_mem_range_idelicNorm E F (↥(IntermediateField.fixedField H'')) 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ x hxN
  have hfix : r x ∈ (IntermediateField.fixedField H'').fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro l hl
    have h := AlgEquiv.restrictNormal_commutes (r x) (↥(IntermediateField.fixedField H'')) ⟨l, hl⟩
    rw [show (r x).restrictNormal ↥(IntermediateField.fixedField H'') = AlgEquiv.restrictNormalHom _ (r x) from rfl, hres,
      AlgEquiv.one_apply] at h
    exact h.symm
  rwa [hLH] at hfix

end S_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq
end P2MW
export P2MW.S_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq (solution)
