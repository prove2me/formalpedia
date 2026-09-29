-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/edd13687-faa9-5169-8114-29962039b602

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Theorems.Thm_RatIdele_exists_norm_apply_eq_ideleNorm_rpow
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_not_exists_forall_apply_mul_heckeGen_eq_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "NumberField MeasureTheory IsDedekindDomain AutomorphicForm P2MW.S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable.AutomorphicForm"
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField.AdelicVolume NumberField.TateGlobal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "classRepTranslates classRepSiegelSet productionPinsGeneral IsGenuineCuspRealizationAt IsArithGenuineCuspRealizable AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff HeckeEigensystem.cNorm HeckeEigensystem.toRawCentral_b SmoothCuspRealizationAt HeckeEigensystem SiegelCovering.glFin_centralScalar_archCentralUnit exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain peterssonIntegral exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc SiegelCovering.coversModCentre_productionPinsGeneral_D_rat SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine ideleNorm_det_globalPoints SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous"
namespace PeterssonHeckeBoundAux
p2m_open "AutomorphicForm"

private def E (v : HeightOneSpectrum (𝓞 ℚ)) : GL (Fin 2) (v.adicCompletion ℚ) →* AdelicGL2 (𝓞 ℚ) ℚ :=
  (AdelicDock.finEmbed (𝓞 ℚ) ℚ).comp (AdelicDock.localEmbed (𝓞 ℚ) ℚ v)

private theorem E_apply (v : HeightOneSpectrum (𝓞 ℚ)) (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    E v k = AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ v k) := rfl

private theorem productionPinsGeneral_U_eq (N : Ideal (𝓞 ℚ)) :
    (productionPinsGeneral ℚ).U N = levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ := rfl

private theorem productionPinsGeneral_gen_eq (v : HeightOneSpectrum (𝓞 ℚ)) :
    (productionPinsGeneral ℚ).gen v = heckeGen (𝓞 ℚ) ℚ v := rfl

private theorem E_mem_U {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ v.asIdeal ∣ N)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (hk' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
      ∈ v.adicCompletionIntegers ℚ) :
    E v k ∈ (productionPinsGeneral ℚ).U N := by
  rw [productionPinsGeneral_U_eq, Subgroup.mem_inf, E_apply]
  have hb : idealBound (𝓞 ℚ) N v = 1 := idealBound_eq_one_of_not_dvd hN hv
  refine ⟨?_, ?_⟩
  · rw [AdelicDock.finEmbed_mem_levelOne_iff, AdelicDock.localEmbed_mem_finiteLevelOne_iff,
      AdelicDock.mem_localLevelOne_iff]
    refine ⟨⟨hk, ?_, ?_⟩, ⟨hk', ?_, ?_⟩⟩ <;> rw [hb]
    · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hk 1 0
    · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using sub_mem (hk 1 1) (one_mem _)
    · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hk' 1 0
    · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using sub_mem (hk' 1 1) (one_mem _)
  · rw [mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]

private theorem heckeGen_eq_E (v : HeightOneSpectrum (𝓞 ℚ)) :
    heckeGen (𝓞 ℚ) ℚ v = E v (diagOne (uniformizerUnit ℚ v)) := by
  rw [E_apply]
  refine Units.ext ?_
  rw [AdelicDock.coe_finEmbed, AdelicDock.coe_localEmbed]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [AdelicDock.mapMatrix_arch_finMat]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]
    exact heckeGenAt_fst (uniformizerUnit ℚ v) i j
  · rw [AdelicDock.mapMatrix_fin_finMat]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, finAdeleEval_apply]
      exact heckeGenAt_snd_apply_self (uniformizerUnit ℚ w) i j
    · rw [AdelicDock.mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ v _ hw]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, finAdeleEval_apply]
      exact heckeGenAt_snd_apply_of_ne (uniformizerUnit ℚ v) hw i j

private theorem mapMatrix_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (r : A) :
    f.mapMatrix (Matrix.scalar (Fin 2) r) = Matrix.scalar (Fin 2) (f r) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

private theorem centralScalar_det_E (v : HeightOneSpectrum (𝓞 ℚ)) (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det (E v k)) =
      E v (Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det k)) := by
  rw [E_apply, E_apply]
  refine Units.ext ?_
  rw [AdelicDock.coe_finEmbed, AdelicDock.coe_localEmbed]
  have hL : ((centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ v k))) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) =
      Matrix.scalar (Fin 2) (Matrix.det (AdelicDock.finMat (𝓞 ℚ) ℚ (AdelicDock.localMat (𝓞 ℚ) ℚ v k))) := rfl
  have hR : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det k) :
      GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.scalar (Fin 2) (Matrix.det (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) := rfl
  rw [hL, hR]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [AdelicDock.mapMatrix_arch_finMat, mapMatrix_scalar, RingHom.map_det, AdelicDock.mapMatrix_arch_finMat,
      Matrix.det_one, Matrix.scalar_apply, Matrix.diagonal_one]
  · rw [AdelicDock.mapMatrix_fin_finMat, mapMatrix_scalar, RingHom.map_det, AdelicDock.mapMatrix_fin_finMat]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_scalar, RingHom.map_det, AdelicDock.mapMatrix_localMat_self, AdelicDock.mapMatrix_localMat_self]
    · rw [mapMatrix_scalar, RingHom.map_det, AdelicDock.mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ v _ hw,
        AdelicDock.mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ v _ hw, Matrix.det_one, Matrix.scalar_apply, Matrix.diagonal_one]

private def weyl (v : HeightOneSpectrum (𝓞 ℚ)) : GL (Fin 2) (v.adicCompletion ℚ) where
  val := Matrix.of ![![0, 1], ![1, 0]]
  inv := Matrix.of ![![0, 1], ![1, 0]]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem weyl_coe (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((weyl v : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.of ![![0, 1], ![1, 0]] := rfl

private theorem weyl_inv_coe (v : HeightOneSpectrum (𝓞 ℚ)) :
    (((weyl v)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.of ![![0, 1], ![1, 0]] := rfl

private theorem weyl_entries_integral (v : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 2) :
    (Matrix.of ![![(0 : v.adicCompletion ℚ), 1], ![1, 0]]) i j ∈ v.adicCompletionIntegers ℚ := by
  fin_cases i <;> fin_cases j
  · exact zero_mem _
  · exact one_mem _
  · exact one_mem _
  · exact zero_mem _

private theorem weyl_mem_U {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ v.asIdeal ∣ N) :
    E v (weyl v) ∈ (productionPinsGeneral ℚ).U N :=
  E_mem_U hN hv (weyl v) (fun i j => by rw [weyl_coe]; exact weyl_entries_integral v i j)
    (fun i j => by rw [weyl_inv_coe]; exact weyl_entries_integral v i j)

private theorem local_identity (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det (diagOne (uniformizerUnit ℚ v))) *
        (diagOne (uniformizerUnit ℚ v))⁻¹ =
      weyl v * diagOne (uniformizerUnit ℚ v) * weyl v := by
  refine Units.ext ?_
  simp only [Units.val_mul, weyl_coe]
  have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det (diagOne (uniformizerUnit ℚ v))) :
      GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.scalar (Fin 2) (Matrix.det (Matrix.diagonal ![((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) :
        v.adicCompletion ℚ), 1])) := rfl
  have h2 : (((diagOne (uniformizerUnit ℚ v))⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(((uniformizerUnit ℚ v)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 1] := rfl
  have h3 : ((diagOne (uniformizerUnit ℚ v) : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 1] := rfl
  rw [h1, h2, h3, Matrix.det_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.vecMul_diagonal]

private theorem centralScalar_det_gen_mul_inv_mem_doubleCoset {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ v.asIdeal ∣ N) :
    centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v)) *
        ((productionPinsGeneral ℚ).gen v)⁻¹ ∈
      HeckePair.doubleCoset ((productionPinsGeneral ℚ).U N) ((productionPinsGeneral ℚ).gen v) := by
  rw [productionPinsGeneral_gen_eq, heckeGen_eq_E, centralScalar_det_E, ← map_inv, ← map_mul, local_identity,
    map_mul, map_mul]
  exact HeckePair.mem_doubleCoset_iff.mpr ⟨_, weyl_mem_U hN hv, _, weyl_mem_U hN hv, rfl⟩

private def tr (x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun z => x (z * g)

private theorem tr_apply (x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g z : AdelicGL2 (𝓞 ℚ) ℚ) : tr x g z = x (z * g) := rfl

private theorem tr_tr (x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g h : AdelicGL2 (𝓞 ℚ) ℚ) : tr (tr x g) h = tr x (h * g) := by
  funext z
  simp only [tr_apply, mul_assoc]

private theorem tr_mul_inv (x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) : tr (tr x g⁻¹) g = x := by
  funext z
  simp only [tr_apply, mul_inv_cancel_right]

private def transSpan (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :=
  Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 ℚ) ℚ => fun z => φ (z * h))

private theorem tr_mem_transSpan (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) : tr φ g ∈ transSpan φ :=
  Submodule.subset_span ⟨g, rfl⟩

private theorem self_mem_transSpan (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : φ ∈ transSpan φ := by
  have h := tr_mem_transSpan φ 1
  have h1 : tr φ 1 = φ := by
    funext z
    simp only [tr_apply, mul_one]
  rwa [h1] at h

private theorem sub_tr_mem_transSpan (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g h : AdelicGL2 (𝓞 ℚ) ℚ) :
    tr φ g - tr φ h ∈ transSpan φ :=
  Submodule.sub_mem _ (tr_mem_transSpan φ g) (tr_mem_transSpan φ h)

private structure PairingData (Φ : HeckeEigensystem ℚ ℂ) where
  R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral
  hR : IsGenuineCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral R
  s : ℝ
  S : Set (AdelicGL2 (𝓞 ℚ) ℚ)
  P : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) →ₗ⋆[ℂ] ℂ
  hs : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
    ‖((R.centralChar ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm ℚ x ^ s
  hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (1 : ℝ) 2}
  hS : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range S
    ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
      {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (1 : ℝ) 2})
  covInt : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ x y : AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
    x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 ℚ) ℚ => fun z => R.toFun (z * h)) →
    y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 ℚ) ℚ => fun z => R.toFun (z * h)) →
    peterssonIntegral ℚ s S (fun z => x (z * g)) (fun z => y (z * g)) =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
        peterssonIntegral ℚ s S x y
  intNe : peterssonIntegral ℚ s S R.toFun R.toFun ≠ 0
  cov : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ x y : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, x ∈ transSpan R.toFun → y ∈ transSpan R.toFun →
    P (tr x g) (tr y g) =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y
  eqInt : ∀ x y : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, x ∈ transSpan R.toFun → y ∈ transSpan R.toFun →
    P x y = peterssonIntegral ℚ s S x y

private theorem nonempty_pairingData (Φ : HeckeEigensystem ℚ ℂ)
    (hΦ : IsArithGenuineCuspRealizable ℚ (productionPinsGeneral ℚ) Φ) : Nonempty (PairingData Φ) := by
  obtain ⟨R, hR⟩ := hΦ
  obtain ⟨hcls, -, hcont⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
      ℚ (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)
      Φ.toRawCentral R
  obtain ⟨σ, hσ⟩ := RatIdele.exists_norm_apply_eq_ideleNorm_rpow _ hcls (hcont hR)
  obtain ⟨S, hSs, hS⟩ :=
    AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc ℚ 1 2
  obtain ⟨hcovInt, hne, hrest⟩ :=
    AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num)
      AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
      Φ Φ R R hR σ (fun x => hσ x) 1 2 one_pos one_lt_two S hSs hS
  obtain ⟨-, P, hPcov, -, hPeq⟩ := hrest rfl
  refine ⟨⟨R, hR, σ, S, P, fun x => hσ x, hSs, hS, hcovInt, hne, ?_, ?_⟩⟩
  · intro g x y hx hy
    exact hPcov g x y (Submodule.mem_sup_left hx) hy
  · intro x y hx hy
    exact hPeq x y (Submodule.mem_sup_left hx) hy

private theorem mul_conj_eq_normSq (z : ℂ) : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := by
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

private theorem petersson_self_eq_ofReal (s : ℝ) (S : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ peterssonIntegral ℚ s S x x = (r : ℂ) := by
  have hpt : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      x g * (starRingEnd ℂ) (x g) *
          ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ) =
        ((Complex.normSq (x g) * NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) :
          ℝ) : ℂ) := by
    intro g
    rw [mul_conj_eq_normSq, Complex.ofReal_mul]
  refine ⟨∫ g in S,
      Complex.normSq (x g) * NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s)
        ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ), ?_, ?_⟩
  · refine integral_nonneg fun g => mul_nonneg (Complex.normSq_nonneg _) ?_
    exact Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _
  · simp only [peterssonIntegral]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun g => hpt g)]
    exact integral_complex_ofReal

section Algebra

variable {Φ : HeckeEigensystem ℚ ℂ} (D : PairingData Φ)

private theorem P_self_eq_ofReal {x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hx : x ∈ transSpan D.R.toFun) :
    ∃ r : ℝ, 0 ≤ r ∧ D.P x x = (r : ℂ) := by
  rw [D.eqInt x x hx hx]
  exact petersson_self_eq_ofReal D.s D.S x

private theorem P_self_ne_zero : D.P D.R.toFun D.R.toFun ≠ 0 := by
  rw [D.eqInt _ _ (self_mem_transSpan _) (self_mem_transSpan _)]
  exact D.intNe

private theorem tr_eq_self_of_mem {u : AdelicGL2 (𝓞 ℚ) ℚ} (hu : u ∈ (productionPinsGeneral ℚ).U Φ.toRawCentral.level) :
    tr D.R.toFun u = D.R.toFun := by
  funext z
  exact D.R.level_invariant z u hu

private theorem cov_factor_eq_one {u : AdelicGL2 (𝓞 ℚ) ℚ} (hu : u ∈ (productionPinsGeneral ℚ).U Φ.toRawCentral.level) :
    ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det u) ^ D.s : ℝ) : ℂ) = 1 := by
  have h := D.cov u D.R.toFun D.R.toFun (self_mem_transSpan _) (self_mem_transSpan _)
  rw [tr_eq_self_of_mem D hu] at h
  have h2 : (((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det u) ^ D.s : ℝ) : ℂ) - 1) *
      D.P D.R.toFun D.R.toFun = 0 := by
    linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 (P_self_ne_zero D)

private theorem exists_tr_eq_of_mem_doubleCoset {gv x : AdelicGL2 (𝓞 ℚ) ℚ}
    (hx : x ∈ HeckePair.doubleCoset ((productionPinsGeneral ℚ).U Φ.toRawCentral.level) gv) :
    ∃ u ∈ (productionPinsGeneral ℚ).U Φ.toRawCentral.level, tr D.R.toFun x = tr (tr D.R.toFun gv) u := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  refine ⟨u, hu, ?_⟩
  funext z
  rw [tr_tr, tr_apply, tr_apply, show z * (u * gv * u') = z * (u * gv) * u' by simp only [mul_assoc]]
  exact D.R.level_invariant _ u' hu'

private theorem P_tr_tr_of_mem {gv x : AdelicGL2 (𝓞 ℚ) ℚ}
    (hx : x ∈ HeckePair.doubleCoset ((productionPinsGeneral ℚ).U Φ.toRawCentral.level) gv) :
    D.P (tr D.R.toFun x) (tr D.R.toFun x) = D.P (tr D.R.toFun gv) (tr D.R.toFun gv) := by
  obtain ⟨u, hu, hxu⟩ := exists_tr_eq_of_mem_doubleCoset D hx
  rw [hxu, D.cov u (tr D.R.toFun gv) (tr D.R.toFun gv) (tr_mem_transSpan _ _) (tr_mem_transSpan _ _),
    cov_factor_eq_one D hu, one_mul]

private theorem P_self_tr_of_mem {gv x : AdelicGL2 (𝓞 ℚ) ℚ}
    (hx : x ∈ HeckePair.doubleCoset ((productionPinsGeneral ℚ).U Φ.toRawCentral.level) gv) :
    D.P D.R.toFun (tr D.R.toFun x) = D.P D.R.toFun (tr D.R.toFun gv) := by
  obtain ⟨u, hu, hxu⟩ := exists_tr_eq_of_mem_doubleCoset D hx
  have h := D.cov u D.R.toFun (tr D.R.toFun gv) (self_mem_transSpan _) (tr_mem_transSpan _ _)
  rw [tr_eq_self_of_mem D hu, cov_factor_eq_one D hu, one_mul] at h
  rw [hxu, h]

private theorem P_tr_self_of_mem {gv x : AdelicGL2 (𝓞 ℚ) ℚ}
    (hx : x ∈ HeckePair.doubleCoset ((productionPinsGeneral ℚ).U Φ.toRawCentral.level) gv) :
    D.P (tr D.R.toFun x) D.R.toFun = D.P (tr D.R.toFun gv) D.R.toFun := by
  obtain ⟨u, hu, hxu⟩ := exists_tr_eq_of_mem_doubleCoset D hx
  have h := D.cov u (tr D.R.toFun gv) D.R.toFun (tr_mem_transSpan _ _) (self_mem_transSpan _)
  rw [tr_eq_self_of_mem D hu, cov_factor_eq_one D hu, one_mul] at h
  rw [hxu, h]

private theorem sum_tr_eq_smul {n : ℕ} {a : ℂ} {reps : Fin n → AdelicGL2 (𝓞 ℚ) ℚ}
    (heig : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∑ i, D.R.toFun (g * reps i) = a * D.R.toFun g) :
    (∑ i, tr D.R.toFun (reps i)) = a • D.R.toFun := by
  funext g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tr_apply]
  exact heig g

private theorem cov_factor_gen_eq_norm_b {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ D.R.exceptionalSet) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v)) ^ D.s =
      ‖Φ.toRawCentral.b v‖ := by
  rw [← D.hs (Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v)),
    D.R.centralChar_det_gen_eq_b hv ⟨_, Subgroup.mem_top _⟩ rfl]

private theorem raw_b_ne_zero {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ D.R.exceptionalSet) : Φ.toRawCentral.b v ≠ 0 := by
  intro h0
  have h := cov_factor_gen_eq_norm_b D hv
  rw [h0, norm_zero] at h
  exact (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) D.s).ne' h

private theorem conj_b_mul_a_eq {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ D.R.exceptionalSet)
    (hF3 : centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v)) *
        ((productionPinsGeneral ℚ).gen v)⁻¹ ∈
      HeckePair.doubleCoset ((productionPinsGeneral ℚ).U Φ.toRawCentral.level) ((productionPinsGeneral ℚ).gen v)) :
    (starRingEnd ℂ) (Φ.toRawCentral.b v) * Φ.a v = (‖Φ.toRawCentral.b v‖ : ℂ) * (starRingEnd ℂ) (Φ.a v) := by
  obtain ⟨reps, hsys, heig⟩ := D.R.hecke_eigen v hv
  have heig' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∑ i, D.R.toFun (g * reps i) = Φ.a v * D.R.toFun g := fun g => heig g
  have hT : (∑ i, tr D.R.toFun (reps i)) = Φ.a v • D.R.toFun := sum_tr_eq_smul D heig'

  have h1 : Φ.a v * D.P D.R.toFun D.R.toFun =
      ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ) * D.P (tr D.R.toFun ((productionPinsGeneral ℚ).gen v)) D.R.toFun := by
    have e1 : D.P (∑ i, tr D.R.toFun (reps i)) D.R.toFun = ∑ i, D.P (tr D.R.toFun (reps i)) D.R.toFun := by
      rw [map_sum D.P (fun i => tr D.R.toFun (reps i)) Finset.univ, LinearMap.coe_sum, Finset.sum_apply]
    rw [hT, map_smul D.P (Φ.a v) D.R.toFun, LinearMap.smul_apply, smul_eq_mul] at e1
    rw [e1, Finset.sum_congr rfl fun i _ => P_tr_self_of_mem D (hsys.mem_doubleCoset i)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

  have h2 : (starRingEnd ℂ) (Φ.a v) * D.P D.R.toFun D.R.toFun =
      ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ) * D.P D.R.toFun (tr D.R.toFun ((productionPinsGeneral ℚ).gen v)) := by
    have e1 : D.P D.R.toFun (∑ i, tr D.R.toFun (reps i)) = ∑ i, D.P D.R.toFun (tr D.R.toFun (reps i)) :=
      map_sum (D.P D.R.toFun) (fun i => tr D.R.toFun (reps i)) Finset.univ
    rw [hT, map_smulₛₗ (D.P D.R.toFun) (Φ.a v) D.R.toFun, smul_eq_mul] at e1
    rw [e1, Finset.sum_congr rfl fun i _ => P_self_tr_of_mem D (hsys.mem_doubleCoset i)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

  have h3 : (starRingEnd ℂ) (Φ.toRawCentral.b v) * D.P (tr D.R.toFun ((productionPinsGeneral ℚ).gen v)) D.R.toFun =
      (‖Φ.toRawCentral.b v‖ : ℂ) * D.P D.R.toFun (tr D.R.toFun ((productionPinsGeneral ℚ).gen v)) := by
    have hc := D.cov ((productionPinsGeneral ℚ).gen v) D.R.toFun (tr D.R.toFun ((productionPinsGeneral ℚ).gen v)⁻¹)
      (self_mem_transSpan _) (tr_mem_transSpan _ _)
    rw [tr_mul_inv, cov_factor_gen_eq_norm_b D hv] at hc
    have hz : tr D.R.toFun (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v)) *
        ((productionPinsGeneral ℚ).gen v)⁻¹) = Φ.toRawCentral.b v • tr D.R.toFun ((productionPinsGeneral ℚ).gen v)⁻¹ := by
      funext g
      rw [tr_apply, Pi.smul_apply, tr_apply, smul_eq_mul, ← mul_assoc, mul_centralScalar_comm, mul_assoc]
      exact D.R.central_eigen v hv _
    have h4 := P_self_tr_of_mem D hF3
    rw [hz, map_smulₛₗ (D.P D.R.toFun) (Φ.toRawCentral.b v) _, smul_eq_mul] at h4
    rw [hc, ← h4]
    ring
  have h5 : ((starRingEnd ℂ) (Φ.toRawCentral.b v) * Φ.a v - (‖Φ.toRawCentral.b v‖ : ℂ) * (starRingEnd ℂ) (Φ.a v)) *
      D.P D.R.toFun D.R.toFun = 0 := by
    linear_combination (starRingEnd ℂ) (Φ.toRawCentral.b v) * h1 - (‖Φ.toRawCentral.b v‖ : ℂ) * h2 +
      ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ) * h3
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact sub_eq_zero.mp h6
  · exact absurd h6 (P_self_ne_zero D)

private theorem exists_sq_eq_nonneg_mul_raw_b {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ D.R.exceptionalSet)
    (hF3 : centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsGeneral ℚ).gen v)) *
        ((productionPinsGeneral ℚ).gen v)⁻¹ ∈
      HeckePair.doubleCoset ((productionPinsGeneral ℚ).U Φ.toRawCentral.level) ((productionPinsGeneral ℚ).gen v)) :
    ∃ t : ℝ, 0 ≤ t ∧ Φ.a v ^ 2 = (t : ℂ) * Φ.toRawCentral.b v := by
  have key := conj_b_mul_a_eq D hv hF3
  have hω0 : Φ.toRawCentral.b v ≠ 0 := raw_b_ne_zero D hv
  have hnormSq : Complex.normSq (Φ.toRawCentral.b v) ≠ 0 := (Complex.normSq_pos.mpr hω0).ne'
  have hnormSqC : (Complex.normSq (Φ.toRawCentral.b v) : ℂ) ≠ 0 := by exact_mod_cast hnormSq
  refine ⟨‖Φ.toRawCentral.b v‖ * Complex.normSq (Φ.a v) / Complex.normSq (Φ.toRawCentral.b v), ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (norm_nonneg _) (Complex.normSq_nonneg _)) (Complex.normSq_nonneg _)
  · have hconj : (starRingEnd ℂ) (Φ.toRawCentral.b v) ≠ 0 := (map_ne_zero _).mpr hω0
    apply mul_right_cancel₀ hconj
    have e1 : Φ.a v ^ 2 * (starRingEnd ℂ) (Φ.toRawCentral.b v) =
        (‖Φ.toRawCentral.b v‖ : ℂ) * (Φ.a v * (starRingEnd ℂ) (Φ.a v)) := by
      linear_combination Φ.a v * key
    rw [e1, mul_conj_eq_normSq, mul_assoc, mul_conj_eq_normSq]
    push_cast
    field_simp

private theorem normSq_a_le_and_eq_case {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ D.R.exceptionalSet) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ,
      HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsGeneral ℚ).U Φ.toRawCentral.level)
        ((productionPinsGeneral ℚ).gen v) reps ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∑ i, D.R.toFun (g * reps i) = Φ.a v * D.R.toFun g) ∧
      Complex.normSq (Φ.a v) ≤ ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℝ) ^ 2 * ‖Φ.toRawCentral.b v‖ ∧
      (Complex.normSq (Φ.a v) = ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℝ) ^ 2 * ‖Φ.toRawCentral.b v‖ →
        ∀ i j, peterssonIntegral ℚ D.s D.S (tr D.R.toFun (reps i) - tr D.R.toFun (reps j))
          (tr D.R.toFun (reps i) - tr D.R.toFun (reps j)) = 0) := by
  obtain ⟨reps, hsys, heig⟩ := D.R.hecke_eigen v hv
  have heig' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∑ i, D.R.toFun (g * reps i) = Φ.a v * D.R.toFun g := fun g => heig g
  refine ⟨reps, hsys, heig', ?_⟩
  have hT : (∑ i, tr D.R.toFun (reps i)) = Φ.a v • D.R.toFun := sum_tr_eq_smul D heig'
  have hcfac := cov_factor_gen_eq_norm_b D hv

  obtain ⟨ρ, hρ0, hρ⟩ := P_self_eq_ofReal D (self_mem_transSpan D.R.toFun)
  have hρpos : 0 < ρ := by
    rcases hρ0.lt_or_eq with h | h
    · exact h
    · exfalso
      apply P_self_ne_zero D
      rw [hρ, ← h, Complex.ofReal_zero]

  have hψψ : ∀ i, D.P (tr D.R.toFun (reps i)) (tr D.R.toFun (reps i)) = (‖Φ.toRawCentral.b v‖ : ℂ) * ρ := by
    intro i
    rw [P_tr_tr_of_mem D (hsys.mem_doubleCoset i),
      D.cov ((productionPinsGeneral ℚ).gen v) D.R.toFun D.R.toFun (self_mem_transSpan _) (self_mem_transSpan _),
      hcfac, hρ]

  have hdiff : ∀ i j, ∃ r : ℝ, 0 ≤ r ∧
      D.P (tr D.R.toFun (reps i) - tr D.R.toFun (reps j)) (tr D.R.toFun (reps i) - tr D.R.toFun (reps j)) = (r : ℂ) :=
    fun i j => P_self_eq_ofReal D (sub_tr_mem_transSpan _ _ _)
  choose r hr0 hr using hdiff

  have hdouble : ∑ i, ∑ j, D.P (tr D.R.toFun (reps i)) (tr D.R.toFun (reps j)) = (Complex.normSq (Φ.a v) : ℂ) * ρ := by
    have e1 : D.P (∑ i, tr D.R.toFun (reps i)) (∑ j, tr D.R.toFun (reps j)) =
        ∑ i, ∑ j, D.P (tr D.R.toFun (reps i)) (tr D.R.toFun (reps j)) := by
      rw [map_sum D.P (fun i => tr D.R.toFun (reps i)) Finset.univ, LinearMap.coe_sum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => map_sum (D.P (tr D.R.toFun (reps i))) (fun j => tr D.R.toFun (reps j)) _
    rw [← e1, hT, map_smul D.P (Φ.a v) D.R.toFun, LinearMap.smul_apply, map_smulₛₗ (D.P D.R.toFun) (Φ.a v) D.R.toFun,
      smul_eq_mul, smul_eq_mul, hρ, ← mul_assoc, mul_conj_eq_normSq]

  have hexpand : ∀ i j, (r i j : ℂ) = (‖Φ.toRawCentral.b v‖ : ℂ) * ρ + (‖Φ.toRawCentral.b v‖ : ℂ) * ρ -
      (D.P (tr D.R.toFun (reps i)) (tr D.R.toFun (reps j)) + D.P (tr D.R.toFun (reps j)) (tr D.R.toFun (reps i))) := by
    intro i j
    rw [← hr i j, map_sub D.P, LinearMap.sub_apply, map_sub (D.P (tr D.R.toFun (reps i))),
      map_sub (D.P (tr D.R.toFun (reps j))), hψψ i, hψψ j]
    ring

  have hsumr : ((∑ i, ∑ j, r i j : ℝ) : ℂ) =
      2 * ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ) ^ 2 * (‖Φ.toRawCentral.b v‖ : ℂ) * ρ -
        2 * (Complex.normSq (Φ.a v) : ℂ) * ρ := by
    push_cast
    simp only [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_comm (f := fun i j => D.P (tr D.R.toFun (reps j)) (tr D.R.toFun (reps i))), hdouble]
    push_cast
    ring
  have hreal : ∑ i, ∑ j, r i j =
      2 * ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℝ) ^ 2 * ‖Φ.toRawCentral.b v‖ * ρ - 2 * Complex.normSq (Φ.a v) * ρ := by
    exact_mod_cast hsumr
  have hsum_nonneg : 0 ≤ ∑ i, ∑ j, r i j := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hr0 i j
  refine ⟨?_, ?_⟩
  · nlinarith [hreal, hsum_nonneg, hρpos]
  · intro heq i j
    have hzero : ∑ i, ∑ j, r i j = 0 := by
      rw [hreal, heq]
      ring
    have hrow : ∑ j, r i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hr0 i j).mp hzero i (Finset.mem_univ i)
    have hij : r i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hr0 i j).mp hrow j (Finset.mem_univ j)
    rw [← D.eqInt _ _ (sub_tr_mem_transSpan _ _ _) (sub_tr_mem_transSpan _ _ _), hr i j, hij, Complex.ofReal_zero]

private theorem exists_forall_doubleCoset_of_tr_eq {v : HeightOneSpectrum (𝓞 ℚ)}
    {reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsGeneral ℚ).U Φ.toRawCentral.level)
      ((productionPinsGeneral ℚ).gen v) reps)
    (heig : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∑ i, D.R.toFun (g * reps i) = Φ.a v * D.R.toFun g)
    (hpt : ∀ i j, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, D.R.toFun (g * reps i) = D.R.toFun (g * reps j)) :
    ∃ cst : ℂ, ∀ y ∈ HeckePair.doubleCoset ((productionPinsGeneral ℚ).U Φ.toRawCentral.level)
      ((productionPinsGeneral ℚ).gen v), ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, D.R.toFun (g * y) = cst * D.R.toFun g := by
  have hm0 : ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (Ideal.absNorm v.asIdeal))
  refine ⟨Φ.a v / ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ), ?_⟩
  have h0 : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, D.R.toFun (g * reps ⟨0, Nat.succ_pos _⟩) =
      Φ.a v / ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ) * D.R.toFun g := by
    intro g
    have hsum := heig g
    rw [Finset.sum_congr rfl fun i _ => hpt i ⟨0, Nat.succ_pos _⟩ g] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [div_mul_eq_mul_div, eq_div_iff hm0]
    linear_combination hsum
  intro y hy g
  obtain ⟨i, hi⟩ := hsys.covers y hy
  rw [QuotientGroup.eq] at hi
  have hyu : y = reps i * (y⁻¹ * reps i)⁻¹ := by group
  rw [hyu, ← mul_assoc, D.R.level_invariant _ _ (inv_mem hi), hpt i ⟨0, Nat.succ_pos _⟩ g, h0 g]

end Algebra

end AutomorphicForm.PeterssonHeckeBoundAux

namespace AutomorphicForm
p2m_export "AutomorphicForm" "classRepTranslates classRepSiegelSet productionPinsGeneral IsGenuineCuspRealizationAt IsArithGenuineCuspRealizable AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff HeckeEigensystem.cNorm HeckeEigensystem.toRawCentral_b SmoothCuspRealizationAt HeckeEigensystem SiegelCovering.glFin_centralScalar_archCentralUnit exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain peterssonIntegral exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc SiegelCovering.coversModCentre_productionPinsGeneral_D_rat SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine ideleNorm_det_globalPoints SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous"
namespace PeterssonHeckeBoundAux
namespace Rigidity
p2m_open "AutomorphicForm"

private theorem span_props {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hc : Continuous φ)
    (hl : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    {ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ}
    (hz : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (centralScalar (𝓞 ℚ) ℚ z * g) = ω z * φ g)
    {x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hx : x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 ℚ) ℚ => fun z => φ (z * h))) :
    Continuous x ∧
      (∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), x (globalPoints (𝓞 ℚ) ℚ γ * g) = x g) ∧
      ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x (centralScalar (𝓞 ℚ) ℚ z * g) = ω z * x g := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    refine ⟨hc.comp (continuous_id.mul continuous_const), fun γ g => ?_, fun z g => ?_⟩
    · show φ (globalPoints (𝓞 ℚ) ℚ γ * g * h) = φ (g * h)
      rw [mul_assoc, hl]
    · show φ (centralScalar (𝓞 ℚ) ℚ z * g * h) = ω z * φ (g * h)
      rw [mul_assoc, hz]
  | zero =>
    exact ⟨continuous_const, fun _ _ => rfl, fun _ _ => by simp⟩
  | add y y' _ _ hy hy' =>
    refine ⟨hy.1.add hy'.1, fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.add_apply, hy.2.1, hy'.2.1]
    · simp only [Pi.add_apply, hy.2.2, hy'.2.2, mul_add]
  | smul c y _ hy =>
    refine ⟨hy.1.const_smul c, fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.smul_apply, hy.2.1]
    · simp only [Pi.smul_apply, smul_eq_mul, hy.2.2]
      ring

private theorem integrand_self_eq (x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (s : ℝ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    x g * (starRingEnd ℂ) (x g) *
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ) =
      ((‖x g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

private theorem weight_pos (s : ℝ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    0 < ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _

private theorem continuous_weight (s : ℝ) :
    Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) :=
  (continuous_ideleNorm_det ℚ).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne'

private theorem integrable_of_petersson_self_ne_zero {s : ℝ} {S : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    {x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (h : peterssonIntegral ℚ s S x x ≠ 0) :
    Integrable (fun g => x g * (starRingEnd ℂ) (x g) *
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ))
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S) := by
  by_contra hni
  exact h (integral_undef hni)

private theorem integrable_normSq_weight_of_petersson_self_ne_zero {s : ℝ} {S : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    {x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (h : peterssonIntegral ℚ s S x x ≠ 0) :
    Integrable (fun g => ‖x g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s))
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S) := by
  refine (integrable_of_petersson_self_ne_zero h).norm.congr (Filter.Eventually.of_forall fun g => ?_)
  show ‖x g * (starRingEnd ℂ) (x g) * _‖ = _
  rw [integrand_self_eq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (mul_nonneg (sq_nonneg _) (weight_pos s g).le)

private theorem integrable_integrand_sub {s : ℝ} {S : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    {u v : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hiu : Integrable (fun g => ‖u g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s))
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S))
    (hiv : Integrable (fun g => ‖v g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s))
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S)) :
    Integrable (fun g => (u g - v g) * (starRingEnd ℂ) (u g - v g) *
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ))
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  refine Integrable.mono' ((hiu.add hiv).const_mul 2) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact (((hu.sub hv).mul (Complex.continuous_conj.comp (hu.sub hv))).mul
      (Complex.continuous_ofReal.comp (continuous_weight s))).aestronglyMeasurable
  · show ‖(u g - v g) * (starRingEnd ℂ) (u g - v g) *
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ)‖ ≤
      2 * (‖u g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) +
        ‖v g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s))
    have h1 := integrand_self_eq (fun g => u g - v g) s g
    rw [h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (weight_pos s g).le)]
    have h2 : ‖u g - v g‖ ^ 2 ≤ 2 * (‖u g‖ ^ 2 + ‖v g‖ ^ 2) := by
      nlinarith [norm_sub_le (u g) (v g), norm_nonneg (u g - v g), norm_nonneg (u g),
        norm_nonneg (v g), sq_nonneg (‖u g‖ - ‖v g‖)]
    calc ‖u g - v g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s)
        ≤ 2 * (‖u g‖ ^ 2 + ‖v g‖ ^ 2) * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) :=
          mul_le_mul_of_nonneg_right h2 (weight_pos s g).le
      _ = 2 * (‖u g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) +
            ‖v g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s)) := by ring

private theorem ae_eq_zero_of_petersson_self_eq_zero {s : ℝ} {S : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    {x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hint : Integrable (fun g => x g * (starRingEnd ℂ) (x g) *
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ))
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S))
    (h0 : peterssonIntegral ℚ s S x x = 0) :
    ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S), x g = 0 := by
  have hint' : Integrable (fun g => ‖x g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s))
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S) := by
    refine hint.norm.congr (Filter.Eventually.of_forall fun g => ?_)
    show ‖x g * (starRingEnd ℂ) (x g) * _‖ = _
    rw [integrand_self_eq, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (sq_nonneg _) (weight_pos s g).le)
  have h1 : (∫ g, ‖x g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s)
      ∂((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S)) = 0 := by
    have h2 : peterssonIntegral ℚ s S x x =
        ((∫ g, ‖x g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s)
          ∂((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S) : ℝ) : ℂ) := by
      unfold peterssonIntegral
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => integrand_self_eq x s g)
    rw [h2] at h0
    exact_mod_cast h0
  have hnn : 0 ≤ᵐ[(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S]
      fun g => ‖x g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) :=
    Filter.Eventually.of_forall fun g => mul_nonneg (sq_nonneg _) (weight_pos s g).le
  have h3 := (integral_eq_zero_iff_of_nonneg_ae hnn hint').mp h1
  filter_upwards [h3] with g hg
  have hg0 : ‖x g‖ ^ 2 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-s) = 0 := hg
  have hg' : ‖x g‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hg0 with h | h
    · exact h
    · exact absurd h (weight_pos s g).ne'
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hg')

private theorem countable_gl2_rat : Countable (GL (Fin 2) ℚ) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  exact Units.val_injective.countable

private theorem measure_inter_slab_eq_zero {α β : ℝ} {S : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hS : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range S
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
        {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    {A : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (hA : MeasurableSet A)
    (hinv : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), globalPoints (𝓞 ℚ) ℚ γ * g ∈ A ↔ g ∈ A)
    (h0 : ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S) A = 0) :
    (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)
      (A ∩ {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) = 0 := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  haveI := countable_gl2_rat
  haveI : Countable (globalPoints (𝓞 ℚ) ℚ).range :=
    (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 ℚ) ℚ)).countable
  set μ := adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ with hμ
  set T : Set (AdelicGL2 (𝓞 ℚ) ℚ) :=
    {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hT
  have hTm : MeasurableSet T :=
    (isClosed_Icc.preimage (continuous_ideleNorm_det ℚ)).measurableSet

  have hTinv : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), globalPoints (𝓞 ℚ) ℚ γ * g ∈ T ↔ g ∈ T := by
    intro γ g
    simp only [hT, Set.mem_setOf_eq, map_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

  set N : Set (AdelicGL2 (𝓞 ℚ) ℚ) := {g | ¬ ∃ γ : (globalPoints (𝓞 ℚ) ℚ).range, γ • g ∈ S} with hN
  set U : Set (AdelicGL2 (𝓞 ℚ) ℚ) :=
    ⋃ γ : (globalPoints (𝓞 ℚ) ℚ).range, (fun g => (γ : AdelicGL2 (𝓞 ℚ) ℚ) * g) ⁻¹' (A ∩ S ∩ T) with hU
  have hNnull : (μ.restrict T) N = 0 := ae_iff.mp hS.ae_covers
  have hB : μ (A ∩ S ∩ T) = 0 := by
    refine le_antisymm ?_ zero_le
    calc μ (A ∩ S ∩ T) ≤ μ (A ∩ S) := measure_mono Set.inter_subset_left
      _ = (μ.restrict S) A := (Measure.restrict_apply hA).symm
      _ = 0 := h0
  have hUnull : μ U = 0 := by
    refine measure_iUnion_null fun γ => ?_
    rw [measure_preimage_mul]
    exact hB
  have hsub : A ∩ T ⊆ N ∪ U := by
    rintro g ⟨hgA, hgT⟩
    by_cases hc : ∃ γ : (globalPoints (𝓞 ℚ) ℚ).range, γ • g ∈ S
    · obtain ⟨γ, hγ⟩ := hc
      refine Or.inr (Set.mem_iUnion.mpr ⟨γ, ?_⟩)
      obtain ⟨c, hc'⟩ := γ
      obtain ⟨γ0, rfl⟩ := MonoidHom.mem_range.mp hc'
      rw [Subgroup.smul_def, smul_eq_mul] at hγ
      exact ⟨⟨(hinv γ0 g).mpr hgA, hγ⟩, (hTinv γ0 g).mpr hgT⟩
    · exact Or.inl hc
  refine le_antisymm ?_ zero_le
  calc μ (A ∩ T) = (μ.restrict T) (A ∩ T) := by
          rw [Measure.restrict_apply (hA.inter hTm), Set.inter_assoc, Set.inter_self]
    _ ≤ (μ.restrict T) (N ∪ U) := measure_mono hsub
    _ ≤ (μ.restrict T) N + (μ.restrict T) U := measure_union_le _ _
    _ = (μ.restrict T) U := by rw [hNnull, zero_add]
    _ ≤ μ U := Measure.restrict_apply_le _ _
    _ = 0 := hUnull

private theorem archDetNorm_centralScalar_archCentralUnit (w₀ : InfinitePlace ℚ) (a : (w₀.Completion)ˣ) :
    archDetNorm w₀ (centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w₀ a)) =
      ‖(a : w₀.Completion)‖ * ‖(a : w₀.Completion)‖ := by
  have h := archDetNorm_centralScalar_mul w₀ a (1 : AdelicGL2 (𝓞 ℚ) ℚ)
  have h1 : archDetNorm w₀ (1 : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    unfold archDetNorm
    rw [map_one, map_one, Units.val_one, Matrix.det_one, norm_one]
  rwa [mul_one, h1, mul_one] at h

private theorem ideleNorm_det_centralScalar_archCentralUnit (w₀ : InfinitePlace ℚ) (hw : w₀.IsReal)
    (a : (w₀.Completion)ˣ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w₀ a))) =
      ‖(a : w₀.Completion)‖ * ‖(a : w₀.Completion)‖ := by
  rw [ideleNorm_det_eq_prod_archDetNorm_pow_mult ℚ _
      (by rw [AutomorphicForm.SiegelCovering.glFin_centralScalar_archCentralUnit]; exact one_mem _),
    Fintype.prod_subsingleton _ w₀, archDetNorm_centralScalar_archCentralUnit]
  have hmult : w₀.mult = 1 := by
    rw [NumberField.InfinitePlace.mult, if_pos hw]
  rw [hmult, pow_one]

private theorem exists_centralScalar_mul_mem_openSlab {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      α < ideleNorm ℚ (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 ℚ) ℚ z * g)) ∧
        ideleNorm ℚ (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 ℚ) ℚ z * g)) < β := by
  have hw : (Rat.infinitePlace).IsReal := Rat.isReal_infinitePlace
  have hN := ideleNorm_pos (F := ℚ) (Matrix.GeneralLinearGroup.det g)
  have hm1 : α < Real.sqrt (α * β) := (Real.lt_sqrt hα.le).mpr (by nlinarith)
  have hm2 : Real.sqrt (α * β) < β := (Real.sqrt_lt' (hα.trans hαβ)).mpr (by nlinarith)
  have hm0 : 0 < Real.sqrt (α * β) := hα.trans hm1
  set t : ℝ := Real.sqrt (Real.sqrt (α * β) / ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) with ht
  have ht2 : t * t * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) = Real.sqrt (α * β) := by
    rw [ht, Real.mul_self_sqrt (div_nonneg hm0.le hN.le), div_mul_cancel₀ _ hN.ne']
  have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hm0 hN)
  have hna : ‖(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t‖ = t := by
    have h1 := (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t)
    rw [← NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply,
      Real.norm_eq_abs, abs_of_pos htpos] at h1
    exact h1.symm
  have ha0 : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t ≠ 0 :=
    norm_pos_iff.mp (by rw [hna]; exact htpos)
  refine ⟨archCentralUnit ℚ Rat.infinitePlace (Units.mk0 _ ha0), ?_⟩
  have hdet : ideleNorm ℚ (Matrix.GeneralLinearGroup.det
      (centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ Rat.infinitePlace (Units.mk0 _ ha0)) * g)) =
        t * t * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
    rw [map_mul, ideleNorm_mul, ideleNorm_det_centralScalar_archCentralUnit _ hw, Units.val_mk0, hna]
  rw [hdet, ht2]
  exact ⟨hm1, hm2⟩

private theorem apply_mul_eq_of_peterssonIntegral_sub_self_eq_zero
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral R)
    (s α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (S : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range S
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hcovV : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ x y : AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 ℚ) ℚ => fun z => R.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 ℚ) ℚ => fun z => R.toFun (z * h)) →
      peterssonIntegral ℚ s S (fun z => x (z * g)) (fun z => y (z * g)) =
        ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
          peterssonIntegral ℚ s S x y)
    (hP0 : peterssonIntegral ℚ s S R.toFun R.toFun ≠ 0)
    (h₁ h₂ : AdelicGL2 (𝓞 ℚ) ℚ)
    (hnull : peterssonIntegral ℚ s S (fun z => R.toFun (z * h₁) - R.toFun (z * h₂))
      (fun z => R.toFun (z * h₁) - R.toFun (z * h₂)) = 0) :
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, R.toFun (g * h₁) = R.toFun (g * h₂) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  have _ := hSs

  have hcont : Continuous R.toFun := hR
  have hls := ((lsXiMemberAt_iff _ _ _ _ _ _ _).mp R.smoothCusp.1.1).1
  have hl : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R.toFun (globalPoints (𝓞 ℚ) ℚ γ * g) = R.toFun g := hls.left_invariant
  set ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ := fun z => ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) with hω
  have hz : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R.toFun (centralScalar (𝓞 ℚ) ℚ z * g) = ω z * R.toFun g :=
    fun z g => hls.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hωne : ∀ z, ω z ≠ 0 := fun z => Units.ne_zero _

  have hmem : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, (fun z => R.toFun (z * h)) ∈
      Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 ℚ) ℚ => fun z => R.toFun (z * h)) :=
    fun h => Submodule.subset_span ⟨h, rfl⟩
  set x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun z => R.toFun (z * h₁) - R.toFun (z * h₂) with hxdef
  have hxmem : x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 ℚ) ℚ => fun z => R.toFun (z * h)) := by
    have := Submodule.sub_mem _ (hmem h₁) (hmem h₂)
    exact this
  obtain ⟨hxc, hxl, hxz⟩ := span_props hcont hl hz hxmem

  have hself : (fun z : AdelicGL2 (𝓞 ℚ) ℚ => R.toFun (z * 1)) = R.toFun := by
    funext z; rw [mul_one]
  have hmem0 : R.toFun ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 ℚ) ℚ => fun z => R.toFun (z * h)) :=
    Submodule.subset_span ⟨1, hself⟩
  have hPne : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ,
      peterssonIntegral ℚ s S (fun z => R.toFun (z * h)) (fun z => R.toFun (z * h)) ≠ 0 := by
    intro h
    have hc := hcovV h R.toFun R.toFun hmem0 hmem0
    rw [hc]
    exact mul_ne_zero (by exact_mod_cast (Real.rpow_pos_of_pos (ideleNorm_pos _) s).ne') hP0
  have hi₁ := integrable_normSq_weight_of_petersson_self_ne_zero (hPne h₁)
  have hi₂ := integrable_normSq_weight_of_petersson_self_ne_zero (hPne h₂)
  have hint := integrable_integrand_sub (s := s) (S := S)
    (hcont.comp (continuous_id.mul continuous_const)) (hcont.comp (continuous_id.mul continuous_const)) hi₁ hi₂

  have hae : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S), x g = 0 :=
    ae_eq_zero_of_petersson_self_eq_zero hint hnull

  set A : Set (AdelicGL2 (𝓞 ℚ) ℚ) := {g | x g ≠ 0} with hAdef
  have hAopen : IsOpen A := isOpen_ne_fun hxc continuous_const
  have hA0 : ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict S) A = 0 := by
    rw [← compl_mem_ae_iff]
    filter_upwards [hae] with g hg
    simp only [hAdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
    exact hg
  have hinv : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), globalPoints (𝓞 ℚ) ℚ γ * g ∈ A ↔ g ∈ A := by
    intro γ g
    simp only [hAdef, Set.mem_setOf_eq, hxl]
  have hslab := measure_inter_slab_eq_zero hS hAopen.measurableSet hinv hA0

  set O : Set (AdelicGL2 (𝓞 ℚ) ℚ) := A ∩ {g | α < ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∧
      ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) < β} with hOdef
  have hOopen : IsOpen O :=
    hAopen.inter ((isOpen_lt continuous_const (continuous_ideleNorm_det ℚ)).inter
      (isOpen_lt (continuous_ideleNorm_det ℚ) continuous_const))
  have hOnull : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) O = 0 := by
    refine le_antisymm ((measure_mono ?_).trans hslab.le) zero_le
    rintro g ⟨hgA, hg1, hg2⟩
    exact ⟨hgA, hg1.le, hg2.le⟩
  have hOempty : O = ∅ := hOopen.eq_empty_of_measure_zero hOnull

  intro g
  obtain ⟨z, hz1, hz2⟩ := exists_centralScalar_mul_mem_openSlab hα hαβ g
  have hzg : centralScalar (𝓞 ℚ) ℚ z * g ∉ A := by
    intro hmemA
    have : centralScalar (𝓞 ℚ) ℚ z * g ∈ O := ⟨hmemA, hz1, hz2⟩
    rw [hOempty] at this
    exact this
  have hx0 : x (centralScalar (𝓞 ℚ) ℚ z * g) = 0 := by
    simp only [hAdef, Set.mem_setOf_eq, not_not] at hzg
    exact hzg
  rw [hxz] at hx0
  have hxg : x g = 0 := (mul_eq_zero.mp hx0).resolve_left (hωne z)
  exact sub_eq_zero.mp hxg

end AutomorphicForm.PeterssonHeckeBoundAux.Rigidity

namespace AutomorphicForm
p2m_export "AutomorphicForm" "classRepTranslates classRepSiegelSet productionPinsGeneral IsGenuineCuspRealizationAt IsArithGenuineCuspRealizable AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff HeckeEigensystem.cNorm HeckeEigensystem.toRawCentral_b SmoothCuspRealizationAt HeckeEigensystem SiegelCovering.glFin_centralScalar_archCentralUnit exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain peterssonIntegral exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc SiegelCovering.coversModCentre_productionPinsGeneral_D_rat SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine ideleNorm_det_globalPoints SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous"
namespace PeterssonHeckeBoundAux
p2m_open "AutomorphicForm"

section Bound

variable {Φ : HeckeEigensystem ℚ ℂ} (D : PairingData Φ)

private noncomputable def levelPrimes (Φ : HeckeEigensystem ℚ ℂ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  (Ideal.finite_factors (I := Φ.level) (by rw [Ne, Ideal.zero_eq_bot]; exact Φ.level_ne_bot)).toFinset

private theorem not_dvd_level_of_not_mem_levelPrimes {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ levelPrimes Φ) :
    ¬ v.asIdeal ∣ Φ.level := fun h => hv ((Set.Finite.mem_toFinset _).mpr h)

private theorem absNorm_pos (v : HeightOneSpectrum (𝓞 ℚ)) : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h

private theorem norm_cNorm (v : HeightOneSpectrum (𝓞 ℚ)) :
    ‖HeckeEigensystem.cNorm v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  simp [HeckeEigensystem.cNorm]

private theorem normSq_a_lt {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ D.R.exceptionalSet) (hlev : ¬ v.asIdeal ∣ Φ.level) :
    Complex.normSq (Φ.a v) < ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℝ) ^ 2 * ‖Φ.toRawCentral.b v‖ := by
  obtain ⟨reps, hsys, heig, hle, heq⟩ := normSq_a_le_and_eq_case D hv
  refine lt_of_le_of_ne hle fun hE => ?_
  have hnull := heq hE
  have hpt : ∀ i j, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, D.R.toFun (g * reps i) = D.R.toFun (g * reps j) := fun i j =>
    AutomorphicForm.PeterssonHeckeBoundAux.Rigidity.apply_mul_eq_of_peterssonIntegral_sub_self_eq_zero Φ D.R D.hR D.s 1 2 one_pos one_lt_two D.S D.hSs
      D.hS D.covInt D.intNe (reps i) (reps j) (hnull i j)
  obtain ⟨cst, hcst⟩ := exists_forall_doubleCoset_of_tr_eq D hsys heig hpt
  refine AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous
    Φ.toRawCentral D.R D.hR v hlev ⟨cst, fun g => ?_⟩
  have h := hcst _ (HeckePair.self_mem_doubleCoset _) g
  rwa [productionPinsGeneral_gen_eq] at h

end Bound

end AutomorphicForm.PeterssonHeckeBoundAux

open _root_.AutomorphicForm _root_.P2MW.S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable.AutomorphicForm AutomorphicForm.PeterssonHeckeBoundAux IsDedekindDomain NumberField in

theorem solution
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ (AutomorphicForm.productionPinsGeneral ℚ) Φ) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), p ∉ S →
        (∃ t : ℝ, 0 ≤ t ∧ Φ.a p ^ 2 = (t : ℂ) * Φ.b p) ∧
        ‖Φ.a p‖ ^ 2 <
          ‖Φ.b p‖ * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) + 2 + ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹) := by
  classical
  obtain ⟨D⟩ := nonempty_pairingData Φ hΦ
  refine ⟨D.R.exceptionalSet ∪ levelPrimes Φ, fun p hp => ?_⟩
  have hexc : p ∉ D.R.exceptionalSet := fun h => hp (Finset.mem_union_left _ h)
  have hlev : ¬ p.asIdeal ∣ Φ.level :=
    not_dvd_level_of_not_mem_levelPrimes fun h => hp (Finset.mem_union_right _ h)
  have hN : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℕ) := absNorm_pos p
  have hF3 := centralScalar_det_gen_mul_inv_mem_doubleCoset Φ.level_ne_bot hlev
  constructor
  · obtain ⟨t, ht, hat⟩ := exists_sq_eq_nonneg_mul_raw_b D hexc hF3
    refine ⟨t / (Ideal.absNorm p.asIdeal : ℕ), div_nonneg ht hN.le, ?_⟩
    rw [hat, HeckeEigensystem.toRawCentral_b]
    simp only [HeckeEigensystem.cNorm]
    push_cast
    ring
  · have hlt := normSq_a_lt D hexc hlev
    rw [HeckeEigensystem.toRawCentral_b, norm_mul, norm_inv, norm_cNorm] at hlt
    have hns : Complex.normSq (Φ.a p) = ‖Φ.a p‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [hns] at hlt
    push_cast at hlt
    have hn0 : ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ≠ 0 := hN.ne'
    have hid : (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) + 1) ^ 2 * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ * ‖Φ.b p‖) =
        ‖Φ.b p‖ * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) + 2 + ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹) := by
      field_simp
      ring
    exact lt_of_lt_of_eq hlt hid

end

end S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable (solution)
