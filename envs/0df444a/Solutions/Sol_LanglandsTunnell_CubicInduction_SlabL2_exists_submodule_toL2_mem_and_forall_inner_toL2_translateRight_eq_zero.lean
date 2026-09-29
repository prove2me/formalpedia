-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c8f0713d-a450-5be8-b5ed-32119085976e

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix IsDedekindDomain NumberField MeasureTheory Filter Topology AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

namespace LTCubicSmoothingInner

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

abbrev 𝔸ℚ : Type := AdeleRing (𝓞 ℚ) ℚ

abbrev G3 : Type := AdelicGL 3 (𝓞 ℚ) ℚ

abbrev Ginf : Type := GL (Fin 3) (InfiniteAdeleRing ℚ)

abbrev Gf : Type := GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)

abbrev μG : Measure G3 := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ

scoped instance secondCountableTopology_adeleRing : SecondCountableTopology 𝔸ℚ :=
  NumberField.AdeleRing.secondCountableTopology ℚ

scoped instance secondCountableTopology_matrix3 : SecondCountableTopology (Matrix (Fin 3) (Fin 3) 𝔸ℚ) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → 𝔸ℚ))

scoped instance secondCountableTopology_G3 : SecondCountableTopology G3 :=
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) 𝔸ℚ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance isHaarMeasure_μG : Measure.IsHaarMeasure μG :=
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ

scoped instance sigmaFinite_μG : SigmaFinite μG := inferInstance

scoped instance sigmaFinite_domainMeasure (a b : ℝ) (Φ₀ : Set G3) : SigmaFinite (domainMeasure a b Φ₀) := by
  rw [domainMeasure_def, slabMeasure_def]; infer_instance

theorem isReal_of_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]; exact Rat.isReal_infinitePlace

theorem continuous_realCoordinate : Continuous realCoordinate :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

def realHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun w : InfinitePlace ℚ =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_of_rat w)).symm.toRingHom

theorem realHom_apply (r : ℝ) (w : InfinitePlace ℚ) :
    realHom r w = (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_of_rat w)).symm r := rfl

theorem continuous_realHom : Continuous realHom := by
  refine continuous_pi fun w => ?_
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_of_rat w)).symm.continuous

theorem realCoordinate_realHom (r : ℝ) : realCoordinate (realHom r) = r :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

theorem realHom_realCoordinate (x : InfiniteAdeleRing ℚ) : realHom (realCoordinate x) = x := by
  funext w
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm_apply_apply
    (x Rat.infinitePlace)

theorem continuous_archEntries : Continuous (archEntries : G3 → Fin 3 → Fin 3 → ℝ) :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_realCoordinate.comp ((continuous_fst.comp (Units.continuous_val.matrix_elem i j)))

def archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) 𝔸ℚ :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : 𝔸ℚ)

theorem mapMatrix_arch_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = g := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = 1 := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

theorem archMat3_one : archMat3 1 = 1 :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ (by rw [mapMatrix_arch_archMat3, map_one])
    (by rw [mapMatrix_fin_archMat3, map_one])

theorem archMat3_mul (g h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    archMat3 (g * h) = archMat3 g * archMat3 h :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

def archToAdelic3 : Ginf →* G3 where
  toFun g :=
    { val := archMat3 g
      inv := archMat3 ((g⁻¹ : Ginf) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

theorem coe_archToAdelic3 (g : Ginf) :
    ((archToAdelic3 g : G3) : Matrix (Fin 3) (Fin 3) 𝔸ℚ) = archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
  rfl

theorem continuous_archToAdelic3 : Continuous archToAdelic3 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : Ginf =>
      (((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : 𝔸ℚ)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  · refine continuous_matrix fun i j => ?_
    have h : Continuous fun a : Ginf => ((a⁻¹ : Ginf) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j :=
      Units.continuous_coe_inv.matrix_elem i j
    exact h.prodMk continuous_const

theorem coe_finEmbedN3 (k : Gf) :
    ((finEmbedN (Fin 3) (𝓞 ℚ) ℚ k : G3) : Matrix (Fin 3) (Fin 3) 𝔸ℚ) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

theorem continuous_finEmbedN3 : Continuous (finEmbedN (Fin 3) (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : Gf =>
      (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : 𝔸ℚ)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : Gf =>
      (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        ((k⁻¹ : Gf) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : 𝔸ℚ)
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

def finPart3 : G3 →* Gf :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

theorem coe_finPart3 (g : G3) :
    ((finPart3 g : Gf) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) 𝔸ℚ) :=
  rfl

theorem coe_componentAt3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : G3) :
    ((componentAt3 (𝓞 ℚ) ℚ v g : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (g : Matrix (Fin 3) (Fin 3) 𝔸ℚ) :=
  rfl

theorem componentAt3_finEmbedN_finPart3 (u : HeightOneSpectrum (𝓞 ℚ)) (g : G3) :
    componentAt3 (𝓞 ℚ) ℚ u (finEmbedN (Fin 3) (𝓞 ℚ) ℚ (finPart3 g)) = componentAt3 (𝓞 ℚ) ℚ u g := by
  apply Units.ext
  rw [coe_componentAt3, coe_componentAt3, coe_finEmbedN3, coe_finPart3, ← RingHom.mapMatrix_comp,
    RingHom.comp_apply, RingHom.comp_apply, mapMatrix_fin_finMatN]

theorem continuous_componentAt3 (v : HeightOneSpectrum (𝓞 ℚ)) : Continuous (componentAt3 (𝓞 ℚ) ℚ v) :=
  Continuous.units_map _
    ((continuous_id.matrix_map
      ((AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ)) :
        Continuous fun m : Matrix (Fin 3) (Fin 3) 𝔸ℚ =>
          m.map ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))))

section Support

variable {T : Set (Fin 3 → Fin 3 → ℝ)}

def unitOf (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) (x : T) : GL (Fin 3) ℝ :=
  have hdet : IsUnit (Matrix.of x.1).det := isUnit_iff_ne_zero.mpr (hTloc x.2)
  ⟨Matrix.of x.1, (Matrix.of x.1)⁻¹, Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet⟩

theorem continuous_unitOf (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) : Continuous (unitOf hTloc) := by
  have hdet : ∀ x : T, IsUnit (Matrix.of x.1).det := fun x => isUnit_iff_ne_zero.mpr (hTloc x.2)
  have hof : Continuous fun x : T => Matrix.of x.1 := continuous_subtype_val
  have hinv : Continuous fun x : T => (Matrix.of x.1)⁻¹ := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hc : ContinuousAt Ring.inverse (Matrix.of x.1).det := by
      simpa using NormedRing.inverse_continuousAt (hdet x).unit
    exact (continuousAt_matrix_inv (Matrix.of x.1) hc).comp (f := fun x : T => Matrix.of x.1) hof.continuousAt
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact hof
  · exact hinv

def liftPair (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) (p : T × Gf) : G3 :=
  archToAdelic3 (Matrix.GeneralLinearGroup.map realHom (unitOf hTloc p.1)) * finEmbedN (Fin 3) (𝓞 ℚ) ℚ p.2

theorem continuous_liftPair (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) : Continuous (liftPair hTloc) := by
  have hmap : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 3) realHom) :=
    Continuous.units_map _
      ((continuous_id.matrix_map continuous_realHom : Continuous fun m : Matrix (Fin 3) (Fin 3) ℝ => m.map realHom))
  exact ((continuous_archToAdelic3.comp (hmap.comp ((continuous_unitOf hTloc).comp continuous_fst))).mul
    (continuous_finEmbedN3.comp continuous_snd))

theorem liftPair_eq (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) (g : G3) (hg : archEntries g ∈ T) :
    liftPair hTloc (⟨archEntries g, hg⟩, finPart3 g) = g := by
  apply Units.ext
  simp only [liftPair, Units.val_mul, coe_archToAdelic3, coe_finEmbedN3]
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_finMatN, mul_one]
    ext i j
    show realHom (archEntries g i j) = ((g : Matrix (Fin 3) (Fin 3) 𝔸ℚ) i j).1
    exact realHom_realCoordinate _
  · rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_finMatN, one_mul]
    rfl

theorem exists_isCompact_superset_of_isSmoothingKernel
    (α : (Fin 3 → Fin 3 → ℝ) → ℂ) (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hα : IsSmoothArchFactor α)
    (hK' : ∀ p, IsOpen (K' p : Set (LocalGL3 p)) ∧ IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ∃ C : Set G3, IsCompact C ∧
      {g : G3 | archEntries g ∈ tsupport α} ∩ {g : G3 | ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p} ⊆ C := by
  set T : Set (Fin 3 → Fin 3 → ℝ) := tsupport α with hT_def
  have hT : IsCompact T := hα.2.1
  have hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0} := hα.2.2
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hT
  set Lf : Set Gf := {k : Gf | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} with hLf_def
  have hLf : IsCompact Lf :=
    (isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem K' (fun p => (hK' p).1)
      (fun p => (hK' p).2) hcof).2
  refine ⟨liftPair hTloc '' ((Set.univ : Set T) ×ˢ Lf),
    (isCompact_univ.prod hLf).image (continuous_liftPair hTloc), ?_⟩
  rintro g ⟨hgA, hgL⟩
  refine ⟨(⟨archEntries g, hgA⟩, finPart3 g), ⟨Set.mem_univ _, ?_⟩, liftPair_eq hTloc g hgA⟩
  intro p
  rw [Set.mem_setOf_eq] at hgL
  show componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ (finPart3 g)) ∈ K' p
  rw [componentAt3_finEmbedN_finPart3]
  exact hgL p

end Support

theorem isClosed_levelSetG (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hK' : ∀ p, IsCompact (K' p : Set (LocalGL3 p))) :
    IsClosed {g : G3 | ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p} := by
  have : {g : G3 | ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p} = ⋂ p, (componentAt3 (𝓞 ℚ) ℚ p) ⁻¹' (K' p) := by
    ext g; simp
  rw [this]
  exact isClosed_iInter fun p => (hK' p).isClosed.preimage (continuous_componentAt3 p)

theorem kernel_facts (φ : G3 → ℂ) (hφ : IsSmoothingKernel φ) :
    Measurable φ ∧ (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ Integrable φ μG := by
  obtain ⟨α, K', hα, hK', hcof, hφeq⟩ := hφ
  set L : Set G3 := {g : G3 | ∀ p, componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p} with hL_def
  have hLclosed : IsClosed L := isClosed_levelSetG K' fun p => (hK' p).2
  have hLmeas : MeasurableSet L := hLclosed.measurableSet
  have hφfun : φ = fun g => α (archEntries g) * L.indicator (fun _ => (1 : ℂ)) g := funext hφeq
  have hαc : Continuous α := hα.1.continuous
  have hmeas : Measurable φ := by
    rw [hφfun]
    exact ((hαc.comp continuous_archEntries).measurable).mul (measurable_const.indicator hLmeas)
  obtain ⟨C, hC⟩ := hαc.bounded_above_of_compact_support hα.2.1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hbound : ∀ g, ‖φ g‖ ≤ C := by
    intro g
    rw [hφeq g, norm_mul]
    refine (mul_le_mul (hC _) (norm_indicator_le_norm_self _ _) (norm_nonneg _) hC0).trans ?_
    simp
  refine ⟨hmeas, ⟨C, hbound⟩, ?_⟩
  obtain ⟨K, hK, hsub⟩ := exists_isCompact_superset_of_isSmoothingKernel α K' hα hK' hcof
  have hsupp : ∀ g, g ∉ K → φ g = 0 := by
    intro g hg
    by_contra hne
    rw [hφeq g] at hne
    have h1 : α (archEntries g) ≠ 0 := left_ne_zero_of_mul hne
    have h2 : L.indicator (fun _ => (1 : ℂ)) g ≠ 0 := right_ne_zero_of_mul hne
    have hgL : g ∈ L := Set.mem_of_indicator_ne_zero h2
    have hgA : archEntries g ∈ tsupport α := subset_tsupport _ h1
    exact hg (hsub ⟨hgA, hgL⟩)
  have hon : IntegrableOn φ K μG :=
    Measure.integrableOn_of_bounded (hK.measure_lt_top).ne hmeas.aestronglyMeasurable
      (ae_of_all _ fun g => hbound g)
  exact hon.integrable_of_forall_notMem_eq_zero hsupp

section Pairing

variable (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set G3)

theorem coeFn_toL2 {F : G3 → ℂ} (hF : F ∈ automorphicSubmodule ω a b Φ₀) :
    (toL2 ω a b Φ₀ ⟨F, hF⟩ : G3 → ℂ) =ᵐ[domainMeasure a b Φ₀] F := by
  rw [toL2_apply]
  exact MemLp.coeFn_toLp _

theorem inner_toL2_eq_integral {A B : G3 → ℂ} (hA : A ∈ automorphicSubmodule ω a b Φ₀)
    (hB : B ∈ automorphicSubmodule ω a b Φ₀) :
    ⟪toL2 ω a b Φ₀ ⟨A, hA⟩, toL2 ω a b Φ₀ ⟨B, hB⟩⟫_ℂ = ∫ x, conj (A x) * B x ∂(domainMeasure a b Φ₀) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 ω a b Φ₀ hA, coeFn_toL2 ω a b Φ₀ hB] with x hxA hxB
  rw [hxA, hxB]
  simp [mul_comm]

theorem integrable_conj_mul {A B : G3 → ℂ} (hA : A ∈ automorphicSubmodule ω a b Φ₀)
    (hB : B ∈ automorphicSubmodule ω a b Φ₀) :
    Integrable (fun x => conj (A x) * B x) (domainMeasure a b Φ₀) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (toL2 ω a b Φ₀ ⟨A, hA⟩) (toL2 ω a b Φ₀ ⟨B, hB⟩)
  refine h.congr ?_
  filter_upwards [coeFn_toL2 ω a b Φ₀ hA, coeFn_toL2 ω a b Φ₀ hB] with x hxA hxB
  rw [hxA, hxB]
  simp [mul_comm]

theorem integral_norm_mul_norm_le {A B : G3 → ℂ} (hA : A ∈ automorphicSubmodule ω a b Φ₀)
    (hB : B ∈ automorphicSubmodule ω a b Φ₀) :
    ∫ x, ‖A x‖ * ‖B x‖ ∂(domainMeasure a b Φ₀) ≤ ‖toL2 ω a b Φ₀ ⟨A, hA⟩‖ * ‖toL2 ω a b Φ₀ ⟨B, hB⟩‖ := by
  set ν := domainMeasure a b Φ₀
  have hAn : MemLp (fun x => ‖A x‖) 2 ν := hA.2.2.norm
  have hBn : MemLp (fun x => ‖B x‖) 2 ν := hB.2.2.norm
  set uA : Lp ℝ 2 ν := hAn.toLp _ with huA
  set uB : Lp ℝ 2 ν := hBn.toLp _ with huB
  have hinner : ⟪uA, uB⟫_ℝ = ∫ x, ‖A x‖ * ‖B x‖ ∂ν := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hAn, MemLp.coeFn_toLp hBn] with x hxA hxB
    rw [hxA, hxB]
    simp [mul_comm]
  have hnA : ‖uA‖ = ‖toL2 ω a b Φ₀ ⟨A, hA⟩‖ := by
    rw [huA, toL2_apply, Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm]
  have hnB : ‖uB‖ = ‖toL2 ω a b Φ₀ ⟨B, hB⟩‖ := by
    rw [huB, toL2_apply, Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm]
  rw [← hinner, ← hnA, ← hnB]
  exact real_inner_le_norm uA uB

end Pairing

section Main

variable (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
  (a b : ℝ) (Φ₀ : Set G3) (hΦ₀ : IsSlabDomain a b Φ₀)
  (G : G3 → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀)
  (hRG : ∀ y : G3, translateRight y G ∈ automorphicSubmodule ω a b Φ₀)
  (F' : G3 → ℂ) (hF' : F' ∈ automorphicSubmodule ω a b Φ₀)
  (φ : G3 → ℂ) (hφ : IsSmoothingKernel φ)
  (hφG : smoothingOperator φ G ∈ automorphicSubmodule ω a b Φ₀)

include hω hΦ₀ hG hφ

theorem main :
    Integrable (fun y => conj (φ y) *
        ⟪toL2 ω a b Φ₀ ⟨translateRight y G, hRG y⟩, toL2 ω a b Φ₀ ⟨F', hF'⟩⟫_ℂ) μG ∧
    ⟪toL2 ω a b Φ₀ ⟨smoothingOperator φ G, hφG⟩, toL2 ω a b Φ₀ ⟨F', hF'⟩⟫_ℂ =
      ∫ y, conj (φ y) * ⟪toL2 ω a b Φ₀ ⟨translateRight y G, hRG y⟩, toL2 ω a b Φ₀ ⟨F', hF'⟩⟫_ℂ ∂μG := by
  set ν := domainMeasure a b Φ₀ with hν

  obtain ⟨hmem, hnorm, hcont⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ G hG
  have hclass : ∀ y, toL2 ω a b Φ₀ ⟨translateRight y G, hRG y⟩ = toL2 ω a b Φ₀ ⟨translateRight y G, (hmem y).1⟩ :=
    fun _ => rfl

  obtain ⟨hφm, ⟨Cφ, hCφ⟩, hφi⟩ := kernel_facts φ hφ
  set uF := toL2 ω a b Φ₀ ⟨F', hF'⟩ with huF
  set u₀ := toL2 ω a b Φ₀ ⟨G, hG.1⟩ with hu₀
  set U : G3 → Carrier a b Φ₀ := fun y => toL2 ω a b Φ₀ ⟨translateRight y G, hRG y⟩ with hU
  have hUcont : Continuous U := hcont
  have hUnorm : ∀ y, ‖U y‖ = ‖u₀‖ := fun y => hnorm y

  have hpair_cont : Continuous fun y => ⟪U y, uF⟫_ℂ := hUcont.inner continuous_const
  have hpair_bdd : ∀ y, ‖⟪U y, uF⟫_ℂ‖ ≤ ‖u₀‖ * ‖uF‖ := fun y => by
    rw [← hUnorm y]; exact norm_inner_le_norm _ _
  have hint : Integrable (fun y => conj (φ y) * ⟪U y, uF⟫_ℂ) μG := by
    have hsm : AEStronglyMeasurable (fun y => conj (φ y)) μG :=
      RCLike.continuous_conj.comp_aestronglyMeasurable hφi.aestronglyMeasurable
    have h1 : Integrable (fun y => conj (φ y)) μG :=
      hφi.norm.mono' hsm (ae_of_all _ fun y => by simp)
    have h2 : Integrable (fun y => ⟪U y, uF⟫_ℂ * conj (φ y)) μG :=
      h1.bdd_mul hpair_cont.aestronglyMeasurable (ae_of_all _ hpair_bdd)
    simpa [mul_comm] using h2
  refine ⟨hint, ?_⟩

  set f : G3 → G3 → ℂ := fun x y => conj (φ y * G (x * y)) * F' x with hf
  have hGc : Continuous G := hG.2.1
  have h1f : AEStronglyMeasurable (Function.uncurry f) (ν.prod μG) := by
    have hA : AEStronglyMeasurable (fun p : G3 × G3 => φ p.2) (ν.prod μG) :=
      (hφm.comp measurable_snd).aestronglyMeasurable
    have hB : AEStronglyMeasurable (fun p : G3 × G3 => G (p.1 * p.2)) (ν.prod μG) :=
      (hGc.comp continuous_mul).aestronglyMeasurable
    have hC : AEStronglyMeasurable (fun p : G3 × G3 => F' p.1) (ν.prod μG) :=
      hF'.2.2.aestronglyMeasurable.comp_fst
    have hAB : AEStronglyMeasurable (fun p : G3 × G3 => conj (φ p.2 * G (p.1 * p.2))) (ν.prod μG) :=
      RCLike.continuous_conj.comp_aestronglyMeasurable (hA.mul hB)
    exact hAB.mul hC
  have hsec : ∀ y, Integrable (fun x => f x y) ν := by
    intro y
    have h := (integrable_conj_mul ω a b Φ₀ (hRG y) hF').const_mul (conj (φ y))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf, translateRight_apply, map_mul]
    ring
  have hnormsec : ∀ y, ∫ x, ‖f x y‖ ∂ν ≤ ‖φ y‖ * (‖u₀‖ * ‖uF‖) := by
    intro y
    have hpt : (fun x => ‖f x y‖) = fun x => ‖φ y‖ * (‖translateRight y G x‖ * ‖F' x‖) := by
      funext x
      simp only [hf, translateRight_apply, norm_mul, map_mul, RCLike.norm_conj]
      ring
    rw [hpt, integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := integral_norm_mul_norm_le ω a b Φ₀ (hRG y) hF'
    rw [hUnorm y] at h
    exact h
  have hInt : Integrable (Function.uncurry f) (ν.prod μG) := by
    rw [MeasureTheory.integrable_prod_iff' h1f]
    refine ⟨ae_of_all _ fun y => hsec y, ?_⟩
    have hsm : AEStronglyMeasurable (fun y => ∫ x, ‖Function.uncurry f (x, y)‖ ∂ν) μG := by
      have := (h1f.norm.prod_swap (μ := μG) (ν := ν)).integral_prod_right'
      simpa using this
    refine Integrable.mono' (hφi.norm.mul_const (‖u₀‖ * ‖uF‖)) hsm (ae_of_all _ fun y => ?_)
    have hnn : 0 ≤ ∫ x, ‖Function.uncurry f (x, y)‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnn]
    exact hnormsec y

  have hLHS : ⟪toL2 ω a b Φ₀ ⟨smoothingOperator φ G, hφG⟩, uF⟫_ℂ =
      ∫ x, ∫ y, f x y ∂μG ∂ν := by
    rw [huF, inner_toL2_eq_integral ω a b Φ₀ hφG hF']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smoothingOperator_apply, hf]
    rw [← integral_conj, ← integral_mul_const]
  have hswap : ∫ x, ∫ y, f x y ∂μG ∂ν = ∫ y, ∫ x, f x y ∂ν ∂μG := integral_integral_swap hInt
  have hinner : ∀ y, ∫ x, f x y ∂ν = conj (φ y) * ⟪U y, uF⟫_ℂ := by
    intro y
    rw [hU, huF, inner_toL2_eq_integral ω a b Φ₀ (hRG y) hF', ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf, translateRight_apply, map_mul]
    ring
  rw [hLHS, hswap]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => hinner y)

end Main

end LTCubicSmoothingInner
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.LTCubicSmoothingInner"

namespace LTCubicHull

open LTCubicSmoothingInner

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

abbrev pins₀ : CarrierPins ℚ :=
  productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

def ν₀ : Measure 𝔸ℚ :=
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

theorem pins₀_ν : pins₀.ν = ν₀ := rfl

scoped instance : IsProbabilityMeasure ν₀ :=
  AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ

theorem ae_mem_box : ∀ᵐ y ∂ν₀, y ∈ AdelicBox.adelicBox ℚ := by
  unfold ν₀ ProbabilityTheory.cond
  exact Measure.ae_smul_measure (ae_restrict_mem (AdelicBox.measurableSet_adelicBox ℚ)) _

def boxHull : Set 𝔸ℚ := (AdelicBox.exists_isCompact_adelicBox_subset ℚ).choose

theorem isCompact_boxHull : IsCompact boxHull :=
  (AdelicBox.exists_isCompact_adelicBox_subset ℚ).choose_spec.1

theorem box_subset_boxHull : AdelicBox.adelicBox ℚ ⊆ boxHull :=
  (AdelicBox.exists_isCompact_adelicBox_subset ℚ).choose_spec.2

theorem ae_mem_boxHull : ∀ᵐ y ∂ν₀, y ∈ boxHull :=
  ae_mem_box.mono fun _ hy => box_subset_boxHull hy

def boxIter (Ψ : 𝔸ℚ → 𝔸ℚ → ℂ) : ℂ := ∫ x, ∫ y, Ψ x y ∂ν₀ ∂ν₀

section Iter

variable {Ψ Ψ' : 𝔸ℚ → 𝔸ℚ → ℂ}

theorem integrable_of_continuous {h : 𝔸ℚ → ℂ} (hh : Continuous h) : Integrable h ν₀ := by
  obtain ⟨B, hB⟩ := isCompact_boxHull.exists_bound_of_continuousOn hh.continuousOn
  exact Integrable.mono' (integrable_const B) hh.aestronglyMeasurable (ae_mem_boxHull.mono fun y hy => hB y hy)

theorem integrable_section (hΨ : Continuous (Function.uncurry Ψ)) (x : 𝔸ℚ) : Integrable (Ψ x) ν₀ :=
  integrable_of_continuous (hΨ.comp (Continuous.prodMk_right x))

theorem continuous_inner (hΨ : Continuous (Function.uncurry Ψ)) :
    Continuous fun x => ∫ y, Ψ x y ∂ν₀ := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  show Tendsto (fun x => ∫ y, Ψ x y ∂ν₀) (𝓝 x₀) (𝓝 (∫ y, Ψ x₀ y ∂ν₀))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨v, hv, hvu⟩ := isCompact_boxHull.mem_uniformity_of_prod (f := Ψ) (s := Set.univ)
    hΨ.continuousOn (Set.mem_univ x₀) (Metric.dist_mem_uniformity hε2)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with x hx
  have hpt : ∀ y ∈ boxHull, ‖Ψ x y - Ψ x₀ y‖ ≤ ε / 2 := fun y hy => by
    have := hvu x hx y hy
    rw [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  rw [dist_eq_norm, ← integral_sub (integrable_section hΨ x) (integrable_section hΨ x₀)]
  have h := norm_integral_le_of_norm_le_const (μ := ν₀) (f := fun y => Ψ x y - Ψ x₀ y) (C := ε / 2)
    (ae_mem_boxHull.mono fun y hy => hpt y hy)
  simp only [probReal_univ, mul_one] at h
  linarith

theorem integrable_innerIntegral (hΨ : Continuous (Function.uncurry Ψ)) :
    Integrable (fun x => ∫ y, Ψ x y ∂ν₀) ν₀ :=
  integrable_of_continuous (continuous_inner hΨ)

theorem boxIter_add (hΨ : Continuous (Function.uncurry Ψ)) (hΨ' : Continuous (Function.uncurry Ψ')) :
    boxIter (fun x y => Ψ x y + Ψ' x y) = boxIter Ψ + boxIter Ψ' := by
  unfold boxIter
  have h1 : (fun x => ∫ y, Ψ x y + Ψ' x y ∂ν₀) = fun x => (∫ y, Ψ x y ∂ν₀) + ∫ y, Ψ' x y ∂ν₀ := by
    funext x
    exact integral_add (integrable_section hΨ x) (integrable_section hΨ' x)
  rw [h1]
  exact integral_add (integrable_innerIntegral hΨ) (integrable_innerIntegral hΨ')

theorem boxIter_const_mul (Ψ : 𝔸ℚ → 𝔸ℚ → ℂ) (c : ℂ) :
    boxIter (fun x y => c * Ψ x y) = c * boxIter Ψ := by
  unfold boxIter
  have h1 : (fun x => ∫ y, c * Ψ x y ∂ν₀) = fun x => c * ∫ y, Ψ x y ∂ν₀ := by
    funext x
    exact integral_const_mul c _
  rw [h1]
  exact integral_const_mul c _

end Iter
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.LTCubicSmoothingInner"

def theta21 (g : G3) (p : 𝔸ℚ × 𝔸ℚ) : G3 := radicalP21 ![p.1, p.2] * g

def theta12 (g : G3) (p : 𝔸ℚ × 𝔸ℚ) : G3 := radicalP12 ![p.1, p.2] * g

theorem continuous_upperUnipotent3 :
    Continuous fun q : 𝔸ℚ × 𝔸ℚ × 𝔸ℚ => (upperUnipotent3 q.1 q.2.1 q.2.2 : G3) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi_iff.2 fun i => continuous_pi_iff.2 fun j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent3, Matrix.of_apply] <;> fun_prop
  · refine continuous_pi_iff.2 fun i => continuous_pi_iff.2 fun j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent3, Matrix.of_apply] <;> fun_prop

theorem continuous_theta21 (g : G3) : Continuous (theta21 g) := by
  have h : Continuous fun p : 𝔸ℚ × 𝔸ℚ => (radicalP21 ![p.1, p.2] : G3) := by
    have := continuous_upperUnipotent3.comp
      (show Continuous fun p : 𝔸ℚ × 𝔸ℚ => ((0 : 𝔸ℚ), p.2, p.1) by fun_prop)
    simpa [radicalP21, Function.comp_def] using this
  exact h.mul continuous_const

theorem continuous_theta12 (g : G3) : Continuous (theta12 g) := by
  have h : Continuous fun p : 𝔸ℚ × 𝔸ℚ => (radicalP12 ![p.1, p.2] : G3) := by
    have := continuous_upperUnipotent3.comp
      (show Continuous fun p : 𝔸ℚ × 𝔸ℚ => (p.1, (0 : 𝔸ℚ), p.2) by fun_prop)
    simpa [radicalP12, Function.comp_def] using this
  exact h.mul continuous_const

theorem isCuspidalAlongP21_iff (F : G3 → ℂ) :
    IsCuspidalAlongP21 pins₀ F ↔ ∀ g : G3, boxIter (fun x y => F (theta21 g (x, y))) = 0 :=
  Iff.rfl

theorem isCuspidalAlongP12_iff (F : G3 → ℂ) :
    IsCuspidalAlongP12 pins₀ F ↔ ∀ g : G3, boxIter (fun x y => F (theta12 g (x, y))) = 0 :=
  Iff.rfl

theorem continuous_uncurry_comp_theta21 {F : G3 → ℂ} (hF : Continuous F) (g : G3) :
    Continuous (Function.uncurry fun x y => F (theta21 g (x, y))) :=
  hF.comp (continuous_theta21 g)

theorem continuous_uncurry_comp_theta12 {F : G3 → ℂ} (hF : Continuous F) (g : G3) :
    Continuous (Function.uncurry fun x y => F (theta12 g (x, y))) :=
  hF.comp (continuous_theta12 g)

section CuspSpace

variable {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} {a b : ℝ} {Φ₀ : Set G3}

theorem add_mem_cuspFunctions {F F' : G3 → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀)
    (hF' : F' ∈ cuspFunctions ω a b Φ₀) : F + F' ∈ cuspFunctions ω a b Φ₀ := by
  refine ⟨Submodule.add_mem _ hF.1 hF'.1, hF.2.1.add hF'.2.1, ?_, ?_⟩
  · rw [isCuspidalAlongP21_iff]
    intro g
    have h := boxIter_add (continuous_uncurry_comp_theta21 hF.2.1 g) (continuous_uncurry_comp_theta21 hF'.2.1 g)
    have h1 := (isCuspidalAlongP21_iff F).1 hF.2.2.1 g
    have h2 := (isCuspidalAlongP21_iff F').1 hF'.2.2.1 g
    simp only [Pi.add_apply]
    rw [h, h1, h2, add_zero]
  · rw [isCuspidalAlongP12_iff]
    intro g
    have h := boxIter_add (continuous_uncurry_comp_theta12 hF.2.1 g) (continuous_uncurry_comp_theta12 hF'.2.1 g)
    have h1 := (isCuspidalAlongP12_iff F).1 hF.2.2.2 g
    have h2 := (isCuspidalAlongP12_iff F').1 hF'.2.2.2 g
    simp only [Pi.add_apply]
    rw [h, h1, h2, add_zero]

theorem smul_mem_cuspFunctions (c : ℂ) {F : G3 → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    c • F ∈ cuspFunctions ω a b Φ₀ := by
  refine ⟨Submodule.smul_mem _ c hF.1, hF.2.1.const_smul c, ?_, ?_⟩
  · rw [isCuspidalAlongP21_iff]
    intro g
    have h1 := (isCuspidalAlongP21_iff F).1 hF.2.2.1 g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [boxIter_const_mul, h1, mul_zero]
  · rw [isCuspidalAlongP12_iff]
    intro g
    have h1 := (isCuspidalAlongP12_iff F).1 hF.2.2.2 g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [boxIter_const_mul, h1, mul_zero]

end CuspSpace
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.LTCubicSmoothingInner"

section Unitary

variable (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
  (a b : ℝ) (Φ₀ : Set G3) (hΦ₀ : IsSlabDomain a b Φ₀)

theorem toL2_add_smul {A B : G3 → ℂ} (hA : A ∈ automorphicSubmodule ω a b Φ₀)
    (hB : B ∈ automorphicSubmodule ω a b Φ₀) (c : ℂ) :
    toL2 ω a b Φ₀ ⟨A, hA⟩ + c • toL2 ω a b Φ₀ ⟨B, hB⟩ =
      toL2 ω a b Φ₀ ⟨A + c • B, Submodule.add_mem _ hA (Submodule.smul_mem _ c hB)⟩ := by
  rw [← map_smul, ← map_add]
  rfl

include hω hΦ₀

theorem norm_translate_add_smul {A B : G3 → ℂ} (hA : A ∈ cuspFunctions ω a b Φ₀)
    (hB : B ∈ cuspFunctions ω a b Φ₀) (g : G3) (c : ℂ)
    (hgA : translateRight g A ∈ automorphicSubmodule ω a b Φ₀)
    (hgB : translateRight g B ∈ automorphicSubmodule ω a b Φ₀) :
    ‖toL2 ω a b Φ₀ ⟨translateRight g A, hgA⟩ + c • toL2 ω a b Φ₀ ⟨translateRight g B, hgB⟩‖ =
      ‖toL2 ω a b Φ₀ ⟨A, hA.1⟩ + c • toL2 ω a b Φ₀ ⟨B, hB.1⟩‖ := by
  have hAB : A + c • B ∈ cuspFunctions ω a b Φ₀ := add_mem_cuspFunctions hA (smul_mem_cuspFunctions c hB)
  obtain ⟨hmem, hnorm, -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ (A + c • B) hAB
  rw [toL2_add_smul, toL2_add_smul]
  have h1 : (⟨translateRight g A + c • translateRight g B,
      Submodule.add_mem _ hgA (Submodule.smul_mem _ c hgB)⟩ : ↥(automorphicSubmodule ω a b Φ₀)) =
      ⟨translateRight g (A + c • B), (hmem g).1⟩ := rfl
  rw [h1, hnorm g]

theorem inner_translate_translate {A B : G3 → ℂ} (hA : A ∈ cuspFunctions ω a b Φ₀)
    (hB : B ∈ cuspFunctions ω a b Φ₀) (g : G3)
    (hgA : translateRight g A ∈ automorphicSubmodule ω a b Φ₀)
    (hgB : translateRight g B ∈ automorphicSubmodule ω a b Φ₀) :
    ⟪toL2 ω a b Φ₀ ⟨translateRight g A, hgA⟩, toL2 ω a b Φ₀ ⟨translateRight g B, hgB⟩⟫_ℂ =
      ⟪toL2 ω a b Φ₀ ⟨A, hA.1⟩, toL2 ω a b Φ₀ ⟨B, hB.1⟩⟫_ℂ := by
  have h := fun c : ℂ => norm_translate_add_smul ω hω a b Φ₀ hΦ₀ hA hB g c hgA hgB
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  have e1 := h 1
  have e2 := h (-1)
  have e3 := h (-RCLike.I)
  have e4 := h RCLike.I
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at e1 e2 e3 e4
  rw [e1, e2, e3, e4]

end Unitary
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.LTCubicSmoothingInner"

section Hull

variable (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
  (a b : ℝ) (Φ₀ : Set G3) (hΦ₀ : IsSlabDomain a b Φ₀)
  (F : G3 → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀)

def OrthF (F' : G3 → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀) : Prop :=
  ∀ (g : G3) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
    ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0

def genSet : Set ↥(automorphicSubmodule ω a b Φ₀) :=
  {f | (f : G3 → ℂ) ∈ cuspFunctions ω a b Φ₀ ∧
    ∀ (F' : G3 → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀), OrthF ω a b Φ₀ F F' hF' →
      ⟪toL2 ω a b Φ₀ f, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0}

def hull : Submodule ℂ (Carrier a b Φ₀) :=
  (Submodule.span ℂ (toL2 ω a b Φ₀ '' genSet ω a b Φ₀ F)).topologicalClosure

theorem toL2_mem_hull_of_mem_genSet {f : ↥(automorphicSubmodule ω a b Φ₀)} (hf : f ∈ genSet ω a b Φ₀ F) :
    toL2 ω a b Φ₀ f ∈ hull ω a b Φ₀ F :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)

theorem inner_eq_zero_of_mem_hull {v : Carrier a b Φ₀} (hv : v ∈ hull ω a b Φ₀ F)
    (F' : G3 → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀) (hO : OrthF ω a b Φ₀ F F' hF') :
    ⟪v, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0 := by
  set u := toL2 ω a b Φ₀ ⟨F', hF'.1⟩ with hu
  set K : Submodule ℂ (Carrier a b Φ₀) := LinearMap.ker ((innerSL ℂ u : Carrier a b Φ₀ →L[ℂ] ℂ) :
    Carrier a b Φ₀ →ₗ[ℂ] ℂ) with hK
  have hKc : IsClosed (K : Set (Carrier a b Φ₀)) := ContinuousLinearMap.isClosed_ker _
  have hle : Submodule.span ℂ (toL2 ω a b Φ₀ '' genSet ω a b Φ₀ F) ≤ K := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    show (innerSL ℂ u) (toL2 ω a b Φ₀ f) = 0
    rw [innerSL_apply_apply, inner_eq_zero_symm]
    exact hf.2 F' hF' hO
  have hmem : v ∈ K := Submodule.topologicalClosure_minimal _ hle hKc hv
  have h0 : (innerSL ℂ u) v = 0 := hmem
  rw [innerSL_apply_apply] at h0
  exact inner_eq_zero_symm.mp h0

include hω hΦ₀ hF

theorem transfer (G : G3 → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀)
    (hGV : toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ hull ω a b Φ₀ F)
    (F' : G3 → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀) (hO : OrthF ω a b Φ₀ F F' hF')
    (g : G3) (hg : translateRight g G ∈ automorphicSubmodule ω a b Φ₀) :
    ⟪toL2 ω a b Φ₀ ⟨translateRight g G, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0 := by
  obtain ⟨hmemF, -, -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ F hF
  obtain ⟨hmemF', -, -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ F' hF'

  set H : G3 → ℂ := translateRight g⁻¹ F' with hH_def
  have hH : H ∈ cuspFunctions ω a b Φ₀ := hmemF' g⁻¹
  have hgH : translateRight g H = F' := by
    rw [hH_def, ← translateRight_mul, mul_inv_cancel, translateRight_one]
  have hgHmem : translateRight g H ∈ automorphicSubmodule ω a b Φ₀ := hgH ▸ hF'.1
  have hOH : OrthF ω a b Φ₀ F H hH := by
    intro h hh
    have hgh : translateRight g (translateRight h F) ∈ automorphicSubmodule ω a b Φ₀ := by
      rw [← translateRight_mul]; exact (hmemF (g * h)).1
    have hu := inner_translate_translate ω hω a b Φ₀ hΦ₀ (hmemF h) hH g hgh hgHmem
    rw [← hu]
    have e1 : (⟨translateRight g (translateRight h F), hgh⟩ : ↥(automorphicSubmodule ω a b Φ₀)) =
        ⟨translateRight (g * h) F, (hmemF (g * h)).1⟩ := Subtype.ext (translateRight_mul g h F).symm
    have e2 : (⟨translateRight g H, hgHmem⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = ⟨F', hF'.1⟩ :=
      Subtype.ext hgH
    rw [e1, e2]
    exact hO (g * h) _

  have h0 : ⟪toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2 ω a b Φ₀ ⟨H, hH.1⟩⟫_ℂ = 0 :=
    inner_eq_zero_of_mem_hull ω a b Φ₀ F hGV H hH hOH
  have hu := inner_translate_translate ω hω a b Φ₀ hΦ₀ hG hH g hg hgHmem
  have e2 : (⟨translateRight g H, hgHmem⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = ⟨F', hF'.1⟩ :=
    Subtype.ext hgH
  rw [e2] at hu
  rw [hu, h0]

theorem toL2_mem_hull : toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ hull ω a b Φ₀ F := by
  refine toL2_mem_hull_of_mem_genSet ω a b Φ₀ F ⟨hF, fun F' hF' hO => ?_⟩
  have h1 : translateRight 1 F ∈ automorphicSubmodule ω a b Φ₀ := by rw [translateRight_one]; exact hF.1
  have e : (⟨translateRight 1 F, h1⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = ⟨F, hF.1⟩ :=
    Subtype.ext (translateRight_one F)
  have := hO 1 h1
  rwa [e] at this

theorem translate_mem_hull (F₂ : G3 → ℂ) (hF₂ : F₂ ∈ cuspFunctions ω a b Φ₀)
    (hV : toL2 ω a b Φ₀ ⟨F₂, hF₂.1⟩ ∈ hull ω a b Φ₀ F)
    (g : G3) (hg : translateRight g F₂ ∈ cuspFunctions ω a b Φ₀) :
    toL2 ω a b Φ₀ ⟨translateRight g F₂, hg.1⟩ ∈ hull ω a b Φ₀ F :=
  toL2_mem_hull_of_mem_genSet ω a b Φ₀ F (f := ⟨translateRight g F₂, hg.1⟩)
    ⟨hg, fun F' hF' hO => transfer ω hω a b Φ₀ hΦ₀ F hF F₂ hF₂ hV F' hF' hO g hg.1⟩

theorem smoothing_mem_hull (F₂ : G3 → ℂ) (hF₂ : F₂ ∈ cuspFunctions ω a b Φ₀)
    (hV : toL2 ω a b Φ₀ ⟨F₂, hF₂.1⟩ ∈ hull ω a b Φ₀ F)
    (φ : G3 → ℂ) (hφ : IsSmoothingKernel φ) (hφF : smoothingOperator φ F₂ ∈ cuspFunctions ω a b Φ₀) :
    toL2 ω a b Φ₀ ⟨smoothingOperator φ F₂, hφF.1⟩ ∈ hull ω a b Φ₀ F := by
  refine toL2_mem_hull_of_mem_genSet ω a b Φ₀ F (f := ⟨smoothingOperator φ F₂, hφF.1⟩)
    ⟨hφF, fun F' hF' hO => ?_⟩
  obtain ⟨hmem₂, -, -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ F₂ hF₂
  obtain ⟨-, hid⟩ := LTCubicSmoothingInner.main ω hω a b Φ₀ hΦ₀ F₂ hF₂ (fun y => (hmem₂ y).1) F' hF'.1 φ hφ hφF.1
  show ⟪toL2 ω a b Φ₀ ⟨smoothingOperator φ F₂, hφF.1⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0
  rw [hid]
  have hzero : ∀ y, ⟪toL2 ω a b Φ₀ ⟨translateRight y F₂, (hmem₂ y).1⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0 :=
    fun y => transfer ω hω a b Φ₀ hΦ₀ F hF F₂ hF₂ hV F' hF' hO y (hmem₂ y).1
  simp [hzero]

omit hω hΦ₀ hF in

theorem hull_eq :
    hull ω a b Φ₀ F = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ hull ω a b Φ₀ F})).topologicalClosure := by
  apply le_antisymm
  · refine Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono fun f hf => ?_))
    exact ⟨(mem_cuspMembers_iff ω a b Φ₀ f).2 hf.1, toL2_mem_hull_of_mem_genSet ω a b Φ₀ F hf⟩
  · refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact hf.2

end Hull
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.LTCubicSmoothingInner"

end LTCubicHull
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.LTCubicSmoothingInner P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.LTCubicHull"

open LTCubicHull in

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ : IsSlabDomain a b Φ₀)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) :
    ∃ V₀ : Submodule ℂ (Carrier a b Φ₀),
      V₀ = (Submodule.span ℂ
        (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V₀})).topologicalClosure ∧
      toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V₀ ∧
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V₀ →
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
          toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V₀) ∧
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V₀ →
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
          toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V₀) ∧
      ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V₀ →
        ∀ (F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀),
          (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
            ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0) →
          ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g G ∈ automorphicSubmodule ω a b Φ₀),
            ⟪toL2 ω a b Φ₀ ⟨translateRight g G, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0 :=
  ⟨hull ω a b Φ₀ F, hull_eq ω a b Φ₀ F, toL2_mem_hull ω _hω a b Φ₀ _hΦ F hF,
    fun F₂ hF₂ hV g hg => translate_mem_hull ω _hω a b Φ₀ _hΦ F hF F₂ hF₂ hV g hg,
    fun F₂ hF₂ hV φ hφ hφF => smoothing_mem_hull ω _hω a b Φ₀ _hΦ F hF F₂ hF₂ hV φ hφ hφF,
    fun G hG hGV F' hF' hO g hg => transfer ω _hω a b Φ₀ _hΦ F hF G hG hGV F' hF' hO g hg⟩

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.LTCubicSmoothingInner P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero.LTCubicHull"

end S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_submodule_toL2_mem_and_forall_inner_toL2_translateRight_eq_zero (solution)
