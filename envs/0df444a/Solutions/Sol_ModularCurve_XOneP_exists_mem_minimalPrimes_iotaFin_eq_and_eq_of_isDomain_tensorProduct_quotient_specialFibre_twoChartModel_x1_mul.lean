-- Prove2me | solution 1 for ModularCurve.XOneP.exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/6686d368-b87a-5799-aab4-2b84dbd4f3d5

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve TopologicalSpace
open scoped TensorProduct

namespace CompDict

def IsMaxPt {X : Type*} [TopologicalSpace X] (x : X) : Prop := ∀ y : X, y ⤳ x → y = x

theorem isMaxPt_genericPoint {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsMaxPt hZ.1.genericPoint := by
  intro y hy
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen : IsGenericPoint hZ.1.genericPoint Z := hZ.1.isGenericPoint_genericPoint hZc

  have hsub : Z ⊆ closure ({y} : Set X) := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hy)) isClosed_closure
  have hirr : IsIrreducible (closure ({y} : Set X)) := isIrreducible_singleton.closure
  have heq : closure ({y} : Set X) = Z := Set.Subset.antisymm (hZ.2 hirr hsub) hsub
  have hy' : IsGenericPoint y Z := by rw [isGenericPoint_def]; exact heq
  exact hy'.eq hgen

theorem isMaxPt_map_of_generalizingMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : GeneralizingMap f) {x : X} (hx : IsMaxPt x) : IsMaxPt (f x) := by
  intro y hy
  obtain ⟨x', hx', rfl⟩ := hf hy
  rw [hx x' hx']

theorem isMaxPt_iff_of_isOpenEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) (x : X) : IsMaxPt (f x) ↔ IsMaxPt x := by
  constructor
  · intro h y hy
    exact hf.injective (h (f y) (hy.map hf.continuous))
  · intro h y hy
    have hmem : y ∈ Set.range f := hy.mem_open hf.isOpen_range ⟨x, rfl⟩
    obtain ⟨x', rfl⟩ := hmem
    rw [hf.isInducing.specializes_iff] at hy
    rw [h x' hy]

theorem isMaxPt_iff_mem_minimalPrimes {C : Type*} [CommRing C] (x : PrimeSpectrum C) :
    IsMaxPt x ↔ x.asIdeal ∈ minimalPrimes C := by
  constructor
  · intro h
    refine ⟨⟨x.2, bot_le⟩, ?_⟩
    rintro q ⟨hq, -⟩ hqx
    have := h ⟨q, hq⟩ ((PrimeSpectrum.le_iff_specializes ⟨q, hq⟩ x).mp hqx)
    rw [← this]
  · intro h y hy
    have hle : y.asIdeal ≤ x.asIdeal := (PrimeSpectrum.le_iff_specializes y x).mpr hy
    exact PrimeSpectrum.ext (le_antisymm hle (h.2 ⟨y.2, bot_le⟩ hle))

section Chart

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
  {B : Type u} [CommRing B] [Algebra A B]
  (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι]
  (hι : ι ≫ c = Spec.map (CommRingCat.ofHom (algebraMap A B)))
  (T : Type u) [CommRing T] [Algebra A T]

noncomputable def chartMap :
    Spec (CommRingCat.of (B ⊗[A] T)) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap A T))) :=
  (pullbackSpecIso A B T).inv ≫
    pullback.map _ _ _ _ ι (𝟙 _) (𝟙 _) (by rw [hι, Category.comp_id]) (by simp)

theorem chartMap_fst :
    chartMap c ι hι T ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ ι := by
  rw [chartMap, Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst]

theorem chartMap_snd :
    chartMap c ι hι T ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (R := T) (S := B ⊗[A] T) (Algebra.TensorProduct.includeRight.toRingHom)) := by
  rw [chartMap, Category.assoc, pullback.lift_snd, Category.comp_id, pullbackSpecIso_inv_snd]
  rfl

scoped instance isOpenImmersion_chartMap : IsOpenImmersion (chartMap c ι hι T) := by
  unfold chartMap
  haveI := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (f := Spec.map (CommRingCat.ofHom (algebraMap A B))) (g := Spec.map (CommRingCat.ofHom (algebraMap A T)))
    (f' := c) (g' := Spec.map (CommRingCat.ofHom (algebraMap A T))) (i₁ := ι) (i₂ := 𝟙 _)
    inferInstance inferInstance hι.symm (Category.id_comp _).symm
  infer_instance

theorem range_chartMap :
    Set.range (chartMap c ι hι T) =
      (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A T)))) ⁻¹' Set.range ι := by
  unfold chartMap
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (by exact (pullbackSpecIso A B T).inv.surjective), Set.image_univ,
    Scheme.Pullback.range_map]
  simp

end Chart

end CompDict
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul.CompDict"

namespace CompDict

theorem comap_mem_minimalPrimes_map_of_tensor_quotient
    {A : Type*} [CommRing A] (I : Ideal A) {B : Type*} [CommRing B] [Algebra A B]
    (𝔔 : Ideal (B ⊗[A] (A ⧸ I))) (h𝔔 : 𝔔 ∈ minimalPrimes (B ⊗[A] (A ⧸ I))) :
    𝔔.comap (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] (A ⧸ I)) ∈
      (I.map (algebraMap A B)).minimalPrimes := by
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I
  let f : (B ⧸ I.map (algebraMap A B)) →+* B ⊗[A] (A ⧸ I) := e.toRingEquiv.toRingHom
  have hfs : Function.Surjective f := e.toRingEquiv.surjective
  have hfi : Function.Injective f := e.toRingEquiv.injective
  have h1 : 𝔔.comap f ∈ minimalPrimes (B ⧸ I.map (algebraMap A B)) := by
    have := Ideal.comap_minimalPrimes_eq_of_surjective hfs ⊥
    rw [Ideal.comap_bot_of_injective _ hfi] at this
    change 𝔔.comap f ∈ (⊥ : Ideal (B ⧸ I.map (algebraMap A B))).minimalPrimes
    rw [this]
    exact ⟨𝔔, h𝔔, rfl⟩
  rw [Ideal.minimalPrimes_eq_comap]
  refine ⟨_, h1, ?_⟩
  rw [Ideal.comap_comap]
  congr 1

theorem eq_map_of_isDomain_of_mem_minimalPrimes
    {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B] (k : Type*) [CommRing k] [Algebra A k]
    (y : Ideal B) [hdom : IsDomain (k ⊗[A] (B ⧸ y))]
    (𝔔 : Ideal (B ⊗[A] k)) (h𝔔 : 𝔔 ∈ minimalPrimes (B ⊗[A] k))
    (hy : 𝔔.comap (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] k) = y) :
    𝔔 = y.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] k) := by

  let e1 : (B ⧸ y) ⊗[A] k ≃ₐ[A] (B ⊗[A] k) ⧸ y.map (algebraMap B (B ⊗[A] k)) :=
    Algebra.TensorProduct.quotientTensorEquiv (R := A) A k B y
  let e2 : k ⊗[A] (B ⧸ y) ≃ₐ[A] (B ⧸ y) ⊗[A] k := Algebra.TensorProduct.comm A k (B ⧸ y)
  have hJ' : y.map (algebraMap B (B ⊗[A] k)) = y.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] k) := rfl
  haveI : IsDomain ((B ⊗[A] k) ⧸ y.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] k)) := by
    rw [← hJ']
    exact MulEquiv.isDomain (k ⊗[A] (B ⧸ y)) (e2.trans e1).symm.toMulEquiv
  have hJp : (y.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] k)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hle : y.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] k) ≤ 𝔔 := by
    rw [Ideal.map_le_iff_le_comap, hy]
  exact le_antisymm (h𝔔.2 ⟨hJp, bot_le⟩ hle) hle

end CompDict
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul.CompDict"

namespace CompDict
open AlgebraicCurve.TwoChartIntegralModel

theorem adjoin_inv_eq {K₀ F : Type u} [Field K₀] [Field F] [Algebra K₀ F] (j : F) :
    IntermediateField.adjoin K₀ ({j⁻¹} : Set F) = IntermediateField.adjoin K₀ ({j} : Set F) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j⁻¹)
    rwa [inv_inv] at this

theorem jInv_not_mem_of_mem_minimalPrimes_chartAlgInf
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (𝔮 : Ideal ↥(chartAlgInf R F j))
    (h𝔮 : 𝔮 ∈ (Ideal.span {algebraMap R ↥(chartAlgInf R F j) ϖ}).minimalPrimes) :
    jInvChartInf R F j ∉ 𝔮 := by
  haveI : Fact (j⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : j ≠ 0)⟩
  have htj' : Transcendental R j⁻¹ := by
    intro halg
    exact htj (by simpa using halg.inv)
  have heq := adjoin_inv_eq (K₀ := K₀) j
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := heq ▸ hFD
  have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := heq ▸ hsep

  obtain ⟨V, -, -, hcentre, -, hgen⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
      R K₀ F j⁻¹ htj' hFD' hsep' ϖ hϖ 𝔮 h𝔮
  intro hmem
  have h1 : ((jInvChartInf R F j : ↥(chartAlgInf R F j)) : F) ∈ V.nonunits := (hcentre _).mp hmem

  have hX : ¬ (Polynomial.C ϖ ∣ (Polynomial.X : Polynomial R)) := by
    rintro ⟨Q, hQ⟩
    have := congrArg Polynomial.leadingCoeff hQ
    rw [Polynomial.leadingCoeff_X, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] at this
    exact hϖ.not_unit (IsUnit.of_mul_eq_one _ this.symm)
  obtain ⟨hj1, hj2⟩ := hgen Polynomial.X hX
  simp only [Polynomial.aeval_X, inv_inv] at hj1 hj2

  have h2 : (j⁻¹ : F) ∈ V.nonunits := h1
  rw [ValuationSubring.inv_mem_nonunits_iff] at h2
  rcases h2 with h0 | hnot
  · exact (Fact.out : j ≠ 0) h0
  · exact hnot hj2

end CompDict
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul.CompDict"

namespace CompDict

theorem exists_isMaxPt_fst_eq_fst
    {A : Type u} [CommRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    (κ : Type u) [Field κ] [Algebra A κ] (k : Type u) [Field k] [Algebra A k] [Algebra κ k] [IsScalarTower A κ k]
    (η : ↥(pullback c (Spec.map (CommRingCat.ofHom (algebraMap A k))))) (hη : CompDict.IsMaxPt η) :
    ∃ θ : ↥(pullback c (Spec.map (CommRingCat.ofHom (algebraMap A κ)))), CompDict.IsMaxPt θ ∧
      (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A κ)))).base θ =
        (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base η := by

  let gκ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A κ))
  let gk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A k))
  let gκk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom (algebraMap κ k))
  have hg : gκk ≫ gκ = gk := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq A κ k]

  let Φ : pullback (pullback.snd c gκ) gκk ≅ pullback c gk :=
    pullbackLeftPullbackSndIso c gκ gκk ≪≫ pullback.congrHom rfl hg
  have hΦ : Φ.hom ≫ pullback.fst c gk = pullback.fst (pullback.snd c gκ) gκk ≫ pullback.fst c gκ := by
    show ((pullbackLeftPullbackSndIso c gκ gκk).hom ≫ (pullback.congrHom rfl hg).hom) ≫ pullback.fst c gk = _
    rw [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

  haveI : Flat gκk := by
    show Flat (Spec.map (CommRingCat.ofHom (algebraMap κ k)))
    rw [Flat.SpecMap_iff]
    show (algebraMap κ k).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  let q : pullback (pullback.snd c gκ) gκk ⟶ pullback c gκ := pullback.fst (pullback.snd c gκ) gκk
  haveI : Flat q := inferInstance
  have hq : GeneralizingMap q.base := Flat.generalizingMap q

  let η' : ↥(pullback (pullback.snd c gκ) gκk) := Φ.inv.base η
  have hΦη : Φ.hom.base η' = η := by
    show (Φ.inv ≫ Φ.hom).base η = η
    rw [Φ.inv_hom_id]; rfl
  have hη' : IsMaxPt η' := by
    rw [← isMaxPt_iff_of_isOpenEmbedding Φ.hom.isOpenEmbedding η', hΦη]
    exact hη
  refine ⟨q.base η', isMaxPt_map_of_generalizingMap hq hη', ?_⟩
  show (q ≫ pullback.fst c gκ).base η' = (pullback.fst c gk).base η
  rw [← hΦ, ← hΦη]
  rfl

end CompDict
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul.CompDict"

namespace CompDictMod
p2m_open "ModularCurve~coeffEmb_jq"

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T]

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  show (jqModC ℚ).map (algebraMap ℚ L) = jqModC L
  exact map_jqModC (algebraMap ℚ L)

end CompDictMod
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul.CompDict"

p2m_open "ModularCurve~coeffEmb_jq" in open CompDict ModularCurve.TwoChart in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (k : Type) [Field k] [IsAlgClosed k] [Algebra A k] (hϖk : algebraMap A k ϖ = 0) :

    (∀ (Z : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
        (hZ : Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))),
        ∃ y : ↥(ModularCurve.TwoChart.XFin A (↥K) j),
          y.asIdeal ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes ∧
          (ModularCurve.TwoChart.ιFin A (↥K) j).base y =
            (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ.1.genericPoint) ∧

    (∀ (y : ↥(ModularCurve.TwoChart.XFin A (↥K) j)),
        y.asIdeal ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes →
        IsDomain (k ⊗[A] (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ y.asIdeal)) →
        ∀ (Z₁ Z₂ : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
          (hZ₁ : Z₁ ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
          (hZ₂ : Z₂ ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))),
          (ModularCurve.TwoChart.ιFin A (↥K) j).base y =
              (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ₁.1.genericPoint →
          (ModularCurve.TwoChart.ιFin A (↥K) j).base y =
              (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ₂.1.genericPoint →
          Z₁ = Z₂) := by
  classical

  set Af := ModularCurve.TwoChart.chartAlgFin A (↥K) j with hAf
  set Ai := ModularCurve.TwoChart.chartAlgInf A (↥K) j with hAi
  set c := ModularCurve.TwoChart.modelTo A (↥K) j with hc
  set ιF := ModularCurve.TwoChart.ιFin A (↥K) j with hιFdef
  set ιI := ModularCurve.TwoChart.ιInf A (↥K) j with hιIdef
  have hιF : ιF ≫ c = Spec.map (CommRingCat.ofHom (algebraMap A ↥Af)) := ModularCurve.TwoChart.ιFin_modelTo A (↥K) j
  have hιI : ιI ≫ c = Spec.map (CommRingCat.ofHom (algebraMap A ↥Ai)) := ModularCurve.TwoChart.ιInf_modelTo A (↥K) j

  have hϖprime : Prime ϖ :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ).prime

  set κ := IsLocalRing.ResidueField A with hκ
  have hmk : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0 := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hϖk, zero_mul]
  letI : Algebra κ k := (Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A k) hmk).toAlgebra
  haveI : IsScalarTower A κ k := IsScalarTower.of_algebraMap_eq (fun a => rfl)

  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hjL : (j : LaurentSeries L) = jqModC L := by rw [hj, CompDictMod.coeffEmb_jq]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    subst hK
    exact (ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC L
      (CongruenceSubgroup.Gamma1 (M * p)) (CompDictMod.T_mem_Gamma1 _) j hjL).2
  haveI := hFD
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsSeparable.of_integral _ _

  have hmapF : (IsLocalRing.maximalIdeal A).map (algebraMap A ↥Af) = Ideal.span {algebraMap A ↥Af ϖ} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]
  have hmapI : (IsLocalRing.maximalIdeal A).map (algebraMap A ↥Ai) = Ideal.span {algebraMap A ↥Ai ϖ} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]

  have key : ∀ (η : ↥(pullback c (specMap A k))), IsMaxPt η →
      ∃ y : ↥(ModularCurve.TwoChart.XFin A (↥K) j),
        y.asIdeal ∈ (Ideal.span {algebraMap A ↥Af ϖ}).minimalPrimes ∧
        ιF.base y = (pullback.fst c (specMap A k)).base η := by
    intro η hη
    obtain ⟨θ, hθ, hθη⟩ := exists_isMaxPt_fst_eq_fst c κ k η hη
    rw [← hθη]

    have hfinrange : (pullback.fst c (specMap A κ)).base θ ∈ Set.range ιF.base := by
      rcases ModularCurve.TwoChart.mem_range_ιFin_or_mem_range_ιInf A (↥K) j
        ((pullback.fst c (specMap A κ)).base θ) with h | h
      · exact h
      · have hθr : θ ∈ Set.range (chartMap c ιI hιI κ) := by
          rw [range_chartMap]; exact h
        obtain ⟨𝔔, rfl⟩ := hθr
        have h𝔔max : IsMaxPt 𝔔 := (isMaxPt_iff_of_isOpenEmbedding (chartMap c ιI hιI κ).isOpenEmbedding 𝔔).mp hθ
        have h𝔔min := (isMaxPt_iff_mem_minimalPrimes 𝔔).mp h𝔔max
        have h𝔮 := comap_mem_minimalPrimes_map_of_tensor_quotient (IsLocalRing.maximalIdeal A) 𝔔.asIdeal h𝔔min
        rw [hmapI] at h𝔮
        have hjinv := jInv_not_mem_of_mem_minimalPrimes_chartAlgInf A L (↥K) j htj hFD hsep ϖ hϖprime _ h𝔮

        set q : ↥(ModularCurve.TwoChart.XInf A (↥K) j) :=
          (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := ↥Ai) (B := κ)))).base 𝔔 with hq
        have hqas : q.asIdeal = 𝔔.asIdeal.comap (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := ↥Ai) (B := κ)) := rfl
        have hqD : q ∈ Set.range (ModularCurve.TwoChart.fInf A (↥K) j).base := by
          letI := (ModularCurve.TwoChart.inclInf A (↥K) j).toRingHom.toAlgebra
          haveI := ModularCurve.TwoChart.isLocalization_away_inclInf A (↥K) j
          have hr := PrimeSpectrum.localization_away_comap_range (R := ↥Ai)
            (↥(ModularCurve.TwoChart.chartAlgMid A (↥K) j)) (ModularCurve.TwoChart.jInvChartInf A (↥K) j)
          have : q ∈ ((PrimeSpectrum.basicOpen (ModularCurve.TwoChart.jInvChartInf A (↥K) j) :
              Opens (PrimeSpectrum ↥Ai)) : Set (PrimeSpectrum ↥Ai)) := by
            change ModularCurve.TwoChart.jInvChartInf A (↥K) j ∉ q.asIdeal
            rw [hqas]
            exact hjinv
          rw [← hr] at this
          exact this
        obtain ⟨z, hz⟩ := hqD
        refine ⟨(ModularCurve.TwoChart.fFin A (↥K) j).base z, ?_⟩
        have h1 : ιF.base ((ModularCurve.TwoChart.fFin A (↥K) j).base z) =
            (ModularCurve.TwoChart.fFin A (↥K) j ≫ ιF).base z := rfl
        rw [h1, hιFdef, ModularCurve.TwoChart.glue_condition A (↥K) j]
        change ιI.base ((ModularCurve.TwoChart.fInf A (↥K) j).base z) = _
        rw [hz, hq]
        change (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ ιI).base 𝔔 = _
        rw [← chartMap_fst c ιI hιI κ]
        rfl

    have hθr : θ ∈ Set.range (chartMap c ιF hιF κ) := by
      rw [range_chartMap]; exact hfinrange
    obtain ⟨𝔔, rfl⟩ := hθr
    have h𝔔max : IsMaxPt 𝔔 := (isMaxPt_iff_of_isOpenEmbedding (chartMap c ιF hιF κ).isOpenEmbedding 𝔔).mp hθ
    have h𝔔min := (isMaxPt_iff_mem_minimalPrimes 𝔔).mp h𝔔max
    have hy := comap_mem_minimalPrimes_map_of_tensor_quotient (IsLocalRing.maximalIdeal A) 𝔔.asIdeal h𝔔min
    rw [hmapF] at hy
    refine ⟨(Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := ↥Af) (B := κ)))).base 𝔔,
      hy, ?_⟩
    change (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ ιF).base 𝔔 = _
    rw [← chartMap_fst c ιF hιF κ]
    rfl
  refine ⟨fun Z hZ => key _ (isMaxPt_genericPoint hZ), ?_⟩

  intro y hy hdom Z₁ Z₂ hZ₁ hZ₂ h₁ h₂
  haveI := hdom

  have hmem : ∀ (Z : Set ↥(pullback c (specMap A k))) (hZ : Z ∈ irreducibleComponents _)
      (hyZ : ιF.base y = (pullback.fst c (specMap A k)).base hZ.1.genericPoint),
      ∃ 𝔔 : ↥(Spec (CommRingCat.of (↥Af ⊗[A] k))), (chartMap c ιF hιF k).base 𝔔 = hZ.1.genericPoint ∧
        𝔔.asIdeal = y.asIdeal.map (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := ↥Af) (B := k)) := by
    intro Z hZ hyZ
    have hr : hZ.1.genericPoint ∈ Set.range (chartMap c ιF hιF k) := by
      rw [range_chartMap]; exact ⟨y, hyZ⟩
    obtain ⟨𝔔, h𝔔⟩ := hr
    refine ⟨𝔔, h𝔔, ?_⟩
    have h𝔔max : IsMaxPt 𝔔 := by
      rw [← isMaxPt_iff_of_isOpenEmbedding (chartMap c ιF hιF k).isOpenEmbedding 𝔔]
      change IsMaxPt ((chartMap c ιF hιF k).base 𝔔)
      rw [h𝔔]; exact isMaxPt_genericPoint hZ
    have h𝔔min := (isMaxPt_iff_mem_minimalPrimes 𝔔).mp h𝔔max

    have hcontr : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := ↥Af) (B := k)))).base 𝔔 = y := by
      apply ιF.isOpenEmbedding.injective
      change (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ ιF).base 𝔔 = _
      rw [← chartMap_fst c ιF hιF k, hyZ, ← h𝔔]
      rfl
    have hcontr' : 𝔔.asIdeal.comap (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := ↥Af) (B := k)) = y.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hcontr
    exact eq_map_of_isDomain_of_mem_minimalPrimes k y.asIdeal 𝔔.asIdeal h𝔔min hcontr'
  obtain ⟨𝔔₁, h𝔔₁, h𝔔₁y⟩ := hmem Z₁ hZ₁ h₁
  obtain ⟨𝔔₂, h𝔔₂, h𝔔₂y⟩ := hmem Z₂ hZ₂ h₂
  have h12 : 𝔔₁ = 𝔔₂ := PrimeSpectrum.ext (h𝔔₁y.trans h𝔔₂y.symm)
  have hgen : hZ₁.1.genericPoint = hZ₂.1.genericPoint := by rw [← h𝔔₁, ← h𝔔₂, h12]
  rw [← hZ₁.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ hZ₁),
    ← hZ₂.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ hZ₂), hgen]

end S_ModularCurve_XOneP_exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_mem_minimalPrimes_iotaFin_eq_and_eq_of_isDomain_tensorProduct_quotient_specialFibre_twoChartModel_x1_mul (solution)
