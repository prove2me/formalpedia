-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/114dc7c2-6faf-5809-89a5-5decbf0b7ab8

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Theorems.Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable_of_coversModCentre
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "NumberField MeasureTheory IsDedekindDomain AutomorphicForm P2MW.S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable_of_coversModCentre.AutomorphicForm"
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField.AdelicVolume NumberField.TateGlobal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsGenuineCuspRealizationAt IsArithGenuineCuspRealizable CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff HeckeEigensystem.cNorm HeckeEigensystem.toRawCentral_b SmoothCuspRealizationAt HeckeEigensystem SiegelCovering.CoversModCentre SiegelCovering.glFin_centralScalar_archCentralUnit peterssonIntegral exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine ideleNorm_det_globalPoints SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt"
namespace PeterssonHeckeBoundGeneralAux
p2m_open "AutomorphicForm"

abbrev wpins (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) :
    CarrierPins F :=
  productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

variable {F : Type} [Field F] [NumberField F]

theorem productionPinsGeneral_U_eq (c₀ u₀ e₁ e₂ : ℝ) (T₀ : Finset (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) :
    (wpins F c₀ u₀ e₁ e₂ T₀).U N = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl

theorem productionPinsGeneral_gen_eq (c₀ u₀ e₁ e₂ : ℝ) (T₀ : Finset (AdelicGL2 (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F)) :
    (wpins F c₀ u₀ e₁ e₂ T₀).gen v = heckeGen (𝓞 F) F v := rfl

def E (v : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (v.adicCompletion F) →* AdelicGL2 (𝓞 F) F :=
  (AdelicDock.finEmbed (𝓞 F) F).comp (AdelicDock.localEmbed (𝓞 F) F v)

theorem E_apply (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F)) :
    E v k = AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v k) := rfl

theorem E_mem_U {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    (k : GL (Fin 2) (v.adicCompletion F))
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (hk' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      ∈ v.adicCompletionIntegers F) :
    E v k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  rw [Subgroup.mem_inf, E_apply]
  have hb : idealBound (𝓞 F) N v = 1 := idealBound_eq_one_of_not_dvd hN hv
  refine ⟨?_, ?_⟩
  · rw [AdelicDock.finEmbed_mem_levelOne_iff, AdelicDock.localEmbed_mem_finiteLevelOne_iff,
      AdelicDock.mem_localLevelOne_iff]
    refine ⟨⟨hk, ?_, ?_⟩, ⟨hk', ?_, ?_⟩⟩ <;> rw [hb]
    · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hk 1 0
    · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using sub_mem (hk 1 1) (one_mem _)
    · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hk' 1 0
    · simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using sub_mem (hk' 1 1) (one_mem _)
  · rw [mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]

theorem heckeGen_eq_E (v : HeightOneSpectrum (𝓞 F)) :
    heckeGen (𝓞 F) F v = E v (diagOne (uniformizerUnit F v)) := by
  rw [E_apply]
  refine Units.ext ?_
  rw [AdelicDock.coe_finEmbed, AdelicDock.coe_localEmbed]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · rw [AdelicDock.mapMatrix_arch_finMat]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]
    exact heckeGenAt_fst (uniformizerUnit F v) i j
  · rw [AdelicDock.mapMatrix_fin_finMat]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, finAdeleEval_apply]
      exact heckeGenAt_snd_apply_self (uniformizerUnit F w) i j
    · rw [AdelicDock.mapMatrix_localMat_of_ne (𝓞 F) F v _ hw]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply, finAdeleEval_apply]
      exact heckeGenAt_snd_apply_of_ne (uniformizerUnit F v) hw i j

theorem mapMatrix_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (r : A) :
    f.mapMatrix (Matrix.scalar (Fin 2) r) = Matrix.scalar (Fin 2) (f r) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

theorem centralScalar_det_E (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F)) :
    centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (E v k)) =
      E v (Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det k)) := by
  rw [E_apply, E_apply]
  refine Units.ext ?_
  rw [AdelicDock.coe_finEmbed, AdelicDock.coe_localEmbed]
  have hL : ((centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det
      (AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v k))) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      Matrix.scalar (Fin 2) (Matrix.det (AdelicDock.finMat (𝓞 F) F (AdelicDock.localMat (𝓞 F) F v k))) := rfl
  have hR : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det k) :
      GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      Matrix.scalar (Fin 2) (Matrix.det (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) := rfl
  rw [hL, hR]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · rw [AdelicDock.mapMatrix_arch_finMat, mapMatrix_scalar, RingHom.map_det, AdelicDock.mapMatrix_arch_finMat,
      Matrix.det_one, Matrix.scalar_apply, Matrix.diagonal_one]
  · rw [AdelicDock.mapMatrix_fin_finMat, mapMatrix_scalar, RingHom.map_det, AdelicDock.mapMatrix_fin_finMat]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_scalar, RingHom.map_det, AdelicDock.mapMatrix_localMat_self, AdelicDock.mapMatrix_localMat_self]
    · rw [mapMatrix_scalar, RingHom.map_det, AdelicDock.mapMatrix_localMat_of_ne (𝓞 F) F v _ hw,
        AdelicDock.mapMatrix_localMat_of_ne (𝓞 F) F v _ hw, Matrix.det_one, Matrix.scalar_apply, Matrix.diagonal_one]

def weyl (v : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (v.adicCompletion F) where
  val := Matrix.of ![![0, 1], ![1, 0]]
  inv := Matrix.of ![![0, 1], ![1, 0]]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_coe (v : HeightOneSpectrum (𝓞 F)) :
    ((weyl v : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      Matrix.of ![![0, 1], ![1, 0]] := rfl

theorem weyl_inv_coe (v : HeightOneSpectrum (𝓞 F)) :
    (((weyl v)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      Matrix.of ![![0, 1], ![1, 0]] := rfl

theorem weyl_entries_integral (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    (Matrix.of ![![(0 : v.adicCompletion F), 1], ![1, 0]]) i j ∈ v.adicCompletionIntegers F := by
  fin_cases i <;> fin_cases j
  · exact zero_mem _
  · exact one_mem _
  · exact one_mem _
  · exact zero_mem _

theorem weyl_mem_U {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) :
    E v (weyl v) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
  E_mem_U hN hv (weyl v) (fun i j => by rw [weyl_coe]; exact weyl_entries_integral v i j)
    (fun i j => by rw [weyl_inv_coe]; exact weyl_entries_integral v i j)

theorem local_identity (v : HeightOneSpectrum (𝓞 F)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det (diagOne (uniformizerUnit F v))) *
        (diagOne (uniformizerUnit F v))⁻¹ =
      weyl v * diagOne (uniformizerUnit F v) * weyl v := by
  refine Units.ext ?_
  simp only [Units.val_mul, weyl_coe]
  have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det (diagOne (uniformizerUnit F v))) :
      GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      Matrix.scalar (Fin 2) (Matrix.det (Matrix.diagonal ![((uniformizerUnit F v : (v.adicCompletion F)ˣ) :
        v.adicCompletion F), 1])) := rfl
  have h2 : (((diagOne (uniformizerUnit F v))⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      Matrix.diagonal ![(((uniformizerUnit F v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), 1] := rfl
  have h3 : ((diagOne (uniformizerUnit F v) : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      Matrix.diagonal ![((uniformizerUnit F v : (v.adicCompletion F)ˣ) : v.adicCompletion F), 1] := rfl
  rw [h1, h2, h3, Matrix.det_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.vecMul_diagonal]

theorem centralScalar_det_gen_mul_inv_mem_doubleCoset {N : Ideal (𝓞 F)} (hN : N ≠ ⊥)
    {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) :
    centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) *
        (heckeGen (𝓞 F) F v)⁻¹ ∈
      HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) := by
  rw [heckeGen_eq_E, centralScalar_det_E, ← map_inv, ← map_mul, local_identity,
    map_mul, map_mul]
  exact HeckePair.mem_doubleCoset_iff.mpr ⟨_, weyl_mem_U hN hv, _, weyl_mem_U hN hv, rfl⟩

def tr (x : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F → ℂ := fun z => x (z * g)

theorem tr_apply (x : AdelicGL2 (𝓞 F) F → ℂ) (g z : AdelicGL2 (𝓞 F) F) : tr x g z = x (z * g) := rfl

theorem tr_tr (x : AdelicGL2 (𝓞 F) F → ℂ) (g h : AdelicGL2 (𝓞 F) F) : tr (tr x g) h = tr x (h * g) := by
  funext z
  simp only [tr_apply, mul_assoc]

theorem tr_mul_inv (x : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : tr (tr x g⁻¹) g = x := by
  funext z
  simp only [tr_apply, mul_inv_cancel_right]

def transSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => φ (z * h))

theorem tr_mem_transSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : tr φ g ∈ transSpan φ :=
  Submodule.subset_span ⟨g, rfl⟩

theorem self_mem_transSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) : φ ∈ transSpan φ := by
  have h := tr_mem_transSpan φ 1
  have h1 : tr φ 1 = φ := by
    funext z
    simp only [tr_apply, mul_one]
  rwa [h1] at h

theorem sub_tr_mem_transSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) (g h : AdelicGL2 (𝓞 F) F) :
    tr φ g - tr φ h ∈ transSpan φ :=
  Submodule.sub_mem _ (tr_mem_transSpan φ g) (tr_mem_transSpan φ h)

structure PairingData (F : Type) [Field F] [NumberField F] (c₀ u₀ e₁ e₂ : ℝ)
    (T₀ : Finset (AdelicGL2 (𝓞 F) F)) (Φ : HeckeEigensystem F ℂ) where
  R : SmoothCuspRealizationAt F (wpins F c₀ u₀ e₁ e₂ T₀) Φ.toRawCentral
  hR : IsGenuineCuspRealizationAt F (wpins F c₀ u₀ e₁ e₂ T₀) Φ.toRawCentral R
  s : ℝ
  S : Set (AdelicGL2 (𝓞 F) F)
  P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ
  hs : ∀ x : (AdeleRing (𝓞 F) F)ˣ,
    ‖((R.centralChar ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F x ^ s
  hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (1 : ℝ) 2}
  hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
    ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
      {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (1 : ℝ) 2})
  covInt : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
    x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) →
    y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) →
    peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
        peterssonIntegral F s S x y
  intNe : peterssonIntegral F s S R.toFun R.toFun ≠ 0
  cov : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ, x ∈ transSpan R.toFun → y ∈ transSpan R.toFun →
    P (tr x g) (tr y g) =
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y
  eqInt : ∀ x y : AdelicGL2 (𝓞 F) F → ℂ, x ∈ transSpan R.toFun → y ∈ transSpan R.toFun →
    P x y = peterssonIntegral F s S x y

theorem nonempty_pairingData {c₀ u₀ e₁ e₂ : ℝ} {T₀ : Finset (AdelicGL2 (𝓞 F) F)}
    (hd : e₁ < e₂) (hcov : CoversModCentre F (⋃ x ∈ T₀, (· * x) '' centreCutSiegelSet F c₀ u₀ e₁ e₂))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F (wpins F c₀ u₀ e₁ e₂ T₀) Φ) : Nonempty (PairingData F c₀ u₀ e₁ e₂ T₀ Φ) := by
  obtain ⟨R, hR⟩ := hΦ
  obtain ⟨hcls, -, hcont⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
      F (⋃ x ∈ T₀, (· * x) '' centreCutSiegelSet F c₀ u₀ e₁ e₂) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)
      Φ.toRawCentral R
  obtain ⟨σ, hσ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F _ hcls (hcont hR)
  obtain ⟨S, hSs, hS⟩ :=
    AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F 1 2
  obtain ⟨hcovInt, hne, hrest⟩ :=
    AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
      F c₀ u₀ e₁ e₂ T₀ hd hcov Φ Φ R R hR σ (fun x => hσ x) 1 2 one_pos one_lt_two S hSs hS
  obtain ⟨-, P, hPcov, -, hPeq⟩ := hrest rfl
  refine ⟨⟨R, hR, σ, S, P, fun x => hσ x, hSs, hS, hcovInt, hne, ?_, ?_⟩⟩
  · intro g x y hx hy
    exact hPcov g x y (Submodule.mem_sup_left hx) hy
  · intro x y hx hy
    exact hPeq x y (Submodule.mem_sup_left hx) hy

theorem mul_conj_eq_normSq (z : ℂ) : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := by
  apply Complex.ext <;> simp [Complex.normSq_apply] ; ring

theorem petersson_self_eq_ofReal (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (x : AdelicGL2 (𝓞 F) F → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ peterssonIntegral F s S x x = (r : ℂ) := by
  have hpt : ∀ g : AdelicGL2 (𝓞 F) F,
      x g * (starRingEnd ℂ) (x g) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ) =
        ((Complex.normSq (x g) * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) :
          ℝ) : ℂ) := by
    intro g
    rw [mul_conj_eq_normSq, Complex.ofReal_mul]
  refine ⟨∫ g in S,
      Complex.normSq (x g) * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ?_, ?_⟩
  · refine integral_nonneg fun g => mul_nonneg (Complex.normSq_nonneg _) ?_
    exact Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _
  · simp only [peterssonIntegral]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun g => hpt g)]
    exact integral_complex_ofReal

section Algebra

variable {c₀ u₀ e₁ e₂ : ℝ} {T₀ : Finset (AdelicGL2 (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ}
  (D : PairingData F c₀ u₀ e₁ e₂ T₀ Φ)

theorem P_self_eq_ofReal {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : x ∈ transSpan D.R.toFun) :
    ∃ r : ℝ, 0 ≤ r ∧ D.P x x = (r : ℂ) := by
  rw [D.eqInt x x hx hx]
  exact petersson_self_eq_ofReal D.s D.S x

theorem P_self_ne_zero : D.P D.R.toFun D.R.toFun ≠ 0 := by
  rw [D.eqInt _ _ (self_mem_transSpan _) (self_mem_transSpan _)]
  exact D.intNe

theorem tr_eq_self_of_mem {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ (wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level) :
    tr D.R.toFun u = D.R.toFun := by
  funext z
  exact D.R.level_invariant z u hu

theorem cov_factor_eq_one {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ (wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level) :
    ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det u) ^ D.s : ℝ) : ℂ) = 1 := by
  have h := D.cov u D.R.toFun D.R.toFun (self_mem_transSpan _) (self_mem_transSpan _)
  rw [tr_eq_self_of_mem D hu] at h
  have h2 : (((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det u) ^ D.s : ℝ) : ℂ) - 1) *
      D.P D.R.toFun D.R.toFun = 0 := by
    linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 (P_self_ne_zero D)

theorem exists_tr_eq_of_mem_doubleCoset {gv x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset ((wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level) gv) :
    ∃ u ∈ (wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level, tr D.R.toFun x = tr (tr D.R.toFun gv) u := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  refine ⟨u, hu, ?_⟩
  funext z
  rw [tr_tr, tr_apply, tr_apply, show z * (u * gv * u') = z * (u * gv) * u' by simp only [mul_assoc]]
  exact D.R.level_invariant _ u' hu'

theorem P_tr_tr_of_mem {gv x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset ((wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level) gv) :
    D.P (tr D.R.toFun x) (tr D.R.toFun x) = D.P (tr D.R.toFun gv) (tr D.R.toFun gv) := by
  obtain ⟨u, hu, hxu⟩ := exists_tr_eq_of_mem_doubleCoset D hx
  rw [hxu, D.cov u (tr D.R.toFun gv) (tr D.R.toFun gv) (tr_mem_transSpan _ _) (tr_mem_transSpan _ _),
    cov_factor_eq_one D hu, one_mul]

theorem P_self_tr_of_mem {gv x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset ((wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level) gv) :
    D.P D.R.toFun (tr D.R.toFun x) = D.P D.R.toFun (tr D.R.toFun gv) := by
  obtain ⟨u, hu, hxu⟩ := exists_tr_eq_of_mem_doubleCoset D hx
  have h := D.cov u D.R.toFun (tr D.R.toFun gv) (self_mem_transSpan _) (tr_mem_transSpan _ _)
  rw [tr_eq_self_of_mem D hu, cov_factor_eq_one D hu, one_mul] at h
  rw [hxu, h]

theorem P_tr_self_of_mem {gv x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset ((wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level) gv) :
    D.P (tr D.R.toFun x) D.R.toFun = D.P (tr D.R.toFun gv) D.R.toFun := by
  obtain ⟨u, hu, hxu⟩ := exists_tr_eq_of_mem_doubleCoset D hx
  have h := D.cov u (tr D.R.toFun gv) D.R.toFun (tr_mem_transSpan _ _) (self_mem_transSpan _)
  rw [tr_eq_self_of_mem D hu, cov_factor_eq_one D hu, one_mul] at h
  rw [hxu, h]

theorem sum_tr_eq_smul {n : ℕ} {a : ℂ} {reps : Fin n → AdelicGL2 (𝓞 F) F}
    (heig : ∀ g : AdelicGL2 (𝓞 F) F, ∑ i, D.R.toFun (g * reps i) = a * D.R.toFun g) :
    (∑ i, tr D.R.toFun (reps i)) = a • D.R.toFun := by
  funext g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tr_apply]
  exact heig g

theorem cov_factor_gen_eq_norm_b {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ D.R.exceptionalSet) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)) ^ D.s =
      ‖Φ.toRawCentral.b v‖ := by
  rw [← D.hs (Matrix.GeneralLinearGroup.det ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)),
    D.R.centralChar_det_gen_eq_b hv ⟨_, Subgroup.mem_top _⟩ rfl]

theorem raw_b_ne_zero {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ D.R.exceptionalSet) : Φ.toRawCentral.b v ≠ 0 := by
  intro h0
  have h := cov_factor_gen_eq_norm_b D hv
  rw [h0, norm_zero] at h
  exact (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) D.s).ne' h

theorem conj_b_mul_a_eq {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ D.R.exceptionalSet)
    (hF3 : centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)) *
        ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)⁻¹ ∈
      HeckePair.doubleCoset ((wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level) ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)) :
    (starRingEnd ℂ) (Φ.toRawCentral.b v) * Φ.a v = (‖Φ.toRawCentral.b v‖ : ℂ) * (starRingEnd ℂ) (Φ.a v) := by
  obtain ⟨reps, hsys, heig⟩ := D.R.hecke_eigen v hv
  have heig' : ∀ g : AdelicGL2 (𝓞 F) F, ∑ i, D.R.toFun (g * reps i) = Φ.a v * D.R.toFun g := fun g => heig g
  have hT : (∑ i, tr D.R.toFun (reps i)) = Φ.a v • D.R.toFun := sum_tr_eq_smul D heig'

  have h1 : Φ.a v * D.P D.R.toFun D.R.toFun =
      ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ) * D.P (tr D.R.toFun ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)) D.R.toFun := by
    have e1 : D.P (∑ i, tr D.R.toFun (reps i)) D.R.toFun = ∑ i, D.P (tr D.R.toFun (reps i)) D.R.toFun := by
      rw [map_sum D.P (fun i => tr D.R.toFun (reps i)) Finset.univ, LinearMap.coe_sum, Finset.sum_apply]
    rw [hT, map_smul D.P (Φ.a v) D.R.toFun, LinearMap.smul_apply, smul_eq_mul] at e1
    rw [e1, Finset.sum_congr rfl fun i _ => P_tr_self_of_mem D (hsys.mem_doubleCoset i)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

  have h2 : (starRingEnd ℂ) (Φ.a v) * D.P D.R.toFun D.R.toFun =
      ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ) * D.P D.R.toFun (tr D.R.toFun ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)) := by
    have e1 : D.P D.R.toFun (∑ i, tr D.R.toFun (reps i)) = ∑ i, D.P D.R.toFun (tr D.R.toFun (reps i)) :=
      map_sum (D.P D.R.toFun) (fun i => tr D.R.toFun (reps i)) Finset.univ
    rw [hT, map_smulₛₗ (D.P D.R.toFun) (Φ.a v) D.R.toFun, smul_eq_mul] at e1
    rw [e1, Finset.sum_congr rfl fun i _ => P_self_tr_of_mem D (hsys.mem_doubleCoset i)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

  have h3 : (starRingEnd ℂ) (Φ.toRawCentral.b v) * D.P (tr D.R.toFun ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)) D.R.toFun =
      (‖Φ.toRawCentral.b v‖ : ℂ) * D.P D.R.toFun (tr D.R.toFun ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)) := by
    have hc := D.cov ((wpins F c₀ u₀ e₁ e₂ T₀).gen v) D.R.toFun (tr D.R.toFun ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)⁻¹)
      (self_mem_transSpan _) (tr_mem_transSpan _ _)
    rw [tr_mul_inv, cov_factor_gen_eq_norm_b D hv] at hc
    have hz : tr D.R.toFun (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)) *
        ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)⁻¹) = Φ.toRawCentral.b v • tr D.R.toFun ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)⁻¹ := by
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

theorem exists_sq_eq_nonneg_mul_raw_b {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ D.R.exceptionalSet)
    (hF3 : centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)) *
        ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)⁻¹ ∈
      HeckePair.doubleCoset ((wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level) ((wpins F c₀ u₀ e₁ e₂ T₀).gen v)) :
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

theorem normSq_a_le_and_eq_case {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ D.R.exceptionalSet) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
      HeckeIntegralSeam.IsHeckeCosetSystem ((wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level)
        ((wpins F c₀ u₀ e₁ e₂ T₀).gen v) reps ∧
      (∀ g : AdelicGL2 (𝓞 F) F, ∑ i, D.R.toFun (g * reps i) = Φ.a v * D.R.toFun g) ∧
      Complex.normSq (Φ.a v) ≤ ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℝ) ^ 2 * ‖Φ.toRawCentral.b v‖ ∧
      (Complex.normSq (Φ.a v) = ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℝ) ^ 2 * ‖Φ.toRawCentral.b v‖ →
        ∀ i j, peterssonIntegral F D.s D.S (tr D.R.toFun (reps i) - tr D.R.toFun (reps j))
          (tr D.R.toFun (reps i) - tr D.R.toFun (reps j)) = 0) := by
  obtain ⟨reps, hsys, heig⟩ := D.R.hecke_eigen v hv
  have heig' : ∀ g : AdelicGL2 (𝓞 F) F, ∑ i, D.R.toFun (g * reps i) = Φ.a v * D.R.toFun g := fun g => heig g
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
      D.cov ((wpins F c₀ u₀ e₁ e₂ T₀).gen v) D.R.toFun D.R.toFun (self_mem_transSpan _) (self_mem_transSpan _),
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

theorem exists_forall_doubleCoset_of_tr_eq {v : HeightOneSpectrum (𝓞 F)}
    {reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem ((wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level)
      ((wpins F c₀ u₀ e₁ e₂ T₀).gen v) reps)
    (heig : ∀ g : AdelicGL2 (𝓞 F) F, ∑ i, D.R.toFun (g * reps i) = Φ.a v * D.R.toFun g)
    (hpt : ∀ i j, ∀ g : AdelicGL2 (𝓞 F) F, D.R.toFun (g * reps i) = D.R.toFun (g * reps j)) :
    ∃ cst : ℂ, ∀ y ∈ HeckePair.doubleCoset ((wpins F c₀ u₀ e₁ e₂ T₀).U Φ.toRawCentral.level)
      ((wpins F c₀ u₀ e₁ e₂ T₀).gen v), ∀ g : AdelicGL2 (𝓞 F) F, D.R.toFun (g * y) = cst * D.R.toFun g := by
  have hm0 : ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (Ideal.absNorm v.asIdeal))
  refine ⟨Φ.a v / ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℂ), ?_⟩
  have h0 : ∀ g : AdelicGL2 (𝓞 F) F, D.R.toFun (g * reps ⟨0, Nat.succ_pos _⟩) =
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

end AutomorphicForm.PeterssonHeckeBoundGeneralAux

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsGenuineCuspRealizationAt IsArithGenuineCuspRealizable CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff HeckeEigensystem.cNorm HeckeEigensystem.toRawCentral_b SmoothCuspRealizationAt HeckeEigensystem SiegelCovering.CoversModCentre SiegelCovering.glFin_centralScalar_archCentralUnit peterssonIntegral exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine ideleNorm_det_globalPoints SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt"
namespace PeterssonHeckeBoundGeneralAux
namespace Rigidity
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

theorem span_props {φ : AdelicGL2 (𝓞 F) F → ℂ} (hc : Continuous φ)
    (hl : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    {ω : (AdeleRing (𝓞 F) F)ˣ → ℂ}
    (hz : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ω z * φ g)
    {x : AdelicGL2 (𝓞 F) F → ℂ}
    (hx : x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => φ (z * h))) :
    Continuous x ∧
      (∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), x (globalPoints (𝓞 F) F γ * g) = x g) ∧
      ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        x (centralScalar (𝓞 F) F z * g) = ω z * x g := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    refine ⟨hc.comp (continuous_id.mul continuous_const), fun γ g => ?_, fun z g => ?_⟩
    · show φ (globalPoints (𝓞 F) F γ * g * h) = φ (g * h)
      rw [mul_assoc, hl]
    · show φ (centralScalar (𝓞 F) F z * g * h) = ω z * φ (g * h)
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

theorem integrand_self_eq (x : AdelicGL2 (𝓞 F) F → ℂ) (s : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    x g * (starRingEnd ℂ) (x g) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ) =
      ((‖x g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem weight_pos (s : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    0 < ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _

theorem continuous_weight (s : ℝ) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) :=
  (continuous_ideleNorm_det F).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne'

theorem integrable_of_petersson_self_ne_zero {s : ℝ} {S : Set (AdelicGL2 (𝓞 F) F)}
    {x : AdelicGL2 (𝓞 F) F → ℂ} (h : peterssonIntegral F s S x x ≠ 0) :
    Integrable (fun g => x g * (starRingEnd ℂ) (x g) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ))
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) := by
  by_contra hni
  exact h (integral_undef hni)

theorem integrable_normSq_weight_of_petersson_self_ne_zero {s : ℝ} {S : Set (AdelicGL2 (𝓞 F) F)}
    {x : AdelicGL2 (𝓞 F) F → ℂ} (h : peterssonIntegral F s S x x ≠ 0) :
    Integrable (fun g => ‖x g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s))
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) := by
  refine (integrable_of_petersson_self_ne_zero h).norm.congr (Filter.Eventually.of_forall fun g => ?_)
  show ‖x g * (starRingEnd ℂ) (x g) * _‖ = _
  rw [integrand_self_eq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (mul_nonneg (sq_nonneg _) (weight_pos s g).le)

theorem integrable_integrand_sub {s : ℝ} {S : Set (AdelicGL2 (𝓞 F) F)}
    {u v : AdelicGL2 (𝓞 F) F → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hiu : Integrable (fun g => ‖u g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s))
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S))
    (hiv : Integrable (fun g => ‖v g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s))
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) :
    Integrable (fun g => (u g - v g) * (starRingEnd ℂ) (u g - v g) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ))
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine Integrable.mono' ((hiu.add hiv).const_mul 2) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact (((hu.sub hv).mul (Complex.continuous_conj.comp (hu.sub hv))).mul
      (Complex.continuous_ofReal.comp (continuous_weight s))).aestronglyMeasurable
  · show ‖(u g - v g) * (starRingEnd ℂ) (u g - v g) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ)‖ ≤
      2 * (‖u g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) +
        ‖v g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s))
    have h1 := integrand_self_eq (fun g => u g - v g) s g
    rw [h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (weight_pos s g).le)]
    have h2 : ‖u g - v g‖ ^ 2 ≤ 2 * (‖u g‖ ^ 2 + ‖v g‖ ^ 2) := by
      nlinarith [norm_sub_le (u g) (v g), norm_nonneg (u g - v g), norm_nonneg (u g),
        norm_nonneg (v g), sq_nonneg (‖u g‖ - ‖v g‖)]
    calc ‖u g - v g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s)
        ≤ 2 * (‖u g‖ ^ 2 + ‖v g‖ ^ 2) * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) :=
          mul_le_mul_of_nonneg_right h2 (weight_pos s g).le
      _ = 2 * (‖u g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) +
            ‖v g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s)) := by ring

theorem ae_eq_zero_of_petersson_self_eq_zero {s : ℝ} {S : Set (AdelicGL2 (𝓞 F) F)}
    {x : AdelicGL2 (𝓞 F) F → ℂ}
    (hint : Integrable (fun g => x g * (starRingEnd ℂ) (x g) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ))
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S))
    (h0 : peterssonIntegral F s S x x = 0) :
    ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S), x g = 0 := by
  have hint' : Integrable (fun g => ‖x g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s))
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) := by
    refine hint.norm.congr (Filter.Eventually.of_forall fun g => ?_)
    show ‖x g * (starRingEnd ℂ) (x g) * _‖ = _
    rw [integrand_self_eq, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (sq_nonneg _) (weight_pos s g).le)
  have h1 : (∫ g, ‖x g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s)
      ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) = 0 := by
    have h2 : peterssonIntegral F s S x x =
        ((∫ g, ‖x g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s)
          ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) : ℝ) : ℂ) := by
      unfold peterssonIntegral
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => integrand_self_eq x s g)
    rw [h2] at h0
    exact_mod_cast h0
  have hnn : 0 ≤ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict S]
      fun g => ‖x g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) :=
    Filter.Eventually.of_forall fun g => mul_nonneg (sq_nonneg _) (weight_pos s g).le
  have h3 := (integral_eq_zero_iff_of_nonneg_ae hnn hint').mp h1
  filter_upwards [h3] with g hg
  have hg0 : ‖x g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) = 0 := hg
  have hg' : ‖x g‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hg0 with h | h
    · exact h
    · exact absurd h (weight_pos s g).ne'
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hg')

theorem countable_gl2 : Countable (GL (Fin 2) F) := by
  haveI : Countable F := by
    let b := Module.finBasis ℚ F
    exact (b.equivFun.injective).countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  exact Units.val_injective.countable

theorem measure_inter_slab_eq_zero {α β : ℝ} {S : Set (AdelicGL2 (𝓞 F) F)}
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    {A : Set (AdelicGL2 (𝓞 F) F)} (hA : MeasurableSet A)
    (hinv : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), globalPoints (𝓞 F) F γ * g ∈ A ↔ g ∈ A)
    (h0 : ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) A = 0) :
    (adelicGLHaar (Fin 2) (𝓞 F) F)
      (A ∩ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) = 0 := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := countable_gl2 (F := F)
  haveI : Countable (globalPoints (𝓞 F) F).range :=
    (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F)).countable
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set T : Set (AdelicGL2 (𝓞 F) F) :=
    {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hT
  have hTm : MeasurableSet T :=
    (isClosed_Icc.preimage (continuous_ideleNorm_det F)).measurableSet

  have hTinv : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), globalPoints (𝓞 F) F γ * g ∈ T ↔ g ∈ T := by
    intro γ g
    simp only [hT, Set.mem_setOf_eq, map_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

  set N : Set (AdelicGL2 (𝓞 F) F) := {g | ¬ ∃ γ : (globalPoints (𝓞 F) F).range, γ • g ∈ S} with hN
  set U : Set (AdelicGL2 (𝓞 F) F) :=
    ⋃ γ : (globalPoints (𝓞 F) F).range, (fun g => (γ : AdelicGL2 (𝓞 F) F) * g) ⁻¹' (A ∩ S ∩ T) with hU
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
    by_cases hc : ∃ γ : (globalPoints (𝓞 F) F).range, γ • g ∈ S
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

theorem archDetNorm_centralScalar_archCentralUnit (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ) :
    archDetNorm w₀ (centralScalar (𝓞 F) F (archCentralUnit F w₀ a)) =
      ‖(a : w₀.Completion)‖ * ‖(a : w₀.Completion)‖ := by
  have h := archDetNorm_centralScalar_mul w₀ a (1 : AdelicGL2 (𝓞 F) F)
  have h1 : archDetNorm w₀ (1 : AdelicGL2 (𝓞 F) F) = 1 := by
    unfold archDetNorm
    rw [map_one, map_one, Units.val_one, Matrix.det_one, norm_one]
  rwa [mul_one, h1, mul_one] at h

theorem archDetNorm_centralScalar_archCentralUnit_of_ne (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ)
    {w : InfinitePlace F} (hw : w ≠ w₀) :
    archDetNorm w (centralScalar (𝓞 F) F (archCentralUnit F w₀ a)) = 1 := by
  unfold archDetNorm
  set s := archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F w₀ a))) with hsdef
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) w.Completion) i j = if i = j then 1 else 0 := by
    intro i j
    simp only [hsdef, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, if_pos rfl]
      exact archCentralUnit_fst_of_ne w₀ a hw
    · rw [centralScalar_apply_ne _ h, if_neg h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp

theorem ideleNorm_det_centralScalar_archCentralUnit (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (archCentralUnit F w₀ a))) =
      (‖(a : w₀.Completion)‖ * ‖(a : w₀.Completion)‖) ^ w₀.mult := by
  rw [ideleNorm_det_eq_prod_archDetNorm_pow_mult F _
      (by rw [AutomorphicForm.SiegelCovering.glFin_centralScalar_archCentralUnit]; exact one_mem _),
    Finset.prod_eq_single w₀ (fun w _ hw => by
      rw [archDetNorm_centralScalar_archCentralUnit_of_ne w₀ a hw, one_pow]) (fun h => absurd (Finset.mem_univ _) h),
    archDetNorm_centralScalar_archCentralUnit]

omit [NumberField F] in

theorem norm_ratCast_completion (w₀ : InfinitePlace F) (q : ℚ) : ‖(q : w₀.Completion)‖ = |(q : ℝ)| := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w₀).norm_map_of_map_zero (map_zero _),
    map_ratCast, Complex.norm_ratCast]

theorem exists_centralScalar_mul_mem_openSlab {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (g : AdelicGL2 (𝓞 F) F) :
    ∃ z : (AdeleRing (𝓞 F) F)ˣ,
      α < ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * g)) ∧
        ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * g)) < β := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hN := ideleNorm_pos (F := F) (Matrix.GeneralLinearGroup.det g)
  set N : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det g) with hNdef
  set m : ℕ := 2 * w₀.mult with hm
  have hm0 : m ≠ 0 := by
    have : 0 < w₀.mult := NumberField.InfinitePlace.mult_pos
    omega

  have hlo : 0 < α / N := div_pos hα hN
  have hlohi : α / N < β / N := div_lt_div_of_pos_right hαβ hN
  have hroot : (α / N) ^ ((m : ℝ)⁻¹) < (β / N) ^ ((m : ℝ)⁻¹) :=
    Real.rpow_lt_rpow hlo.le hlohi (inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hm0))
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn hroot
  have hlo' : 0 < (α / N) ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos hlo _
  have htpos : (0 : ℝ) < t := hlo'.trans ht1
  have htm1 : α / N < (t : ℝ) ^ m := by
    have h := pow_lt_pow_left₀ ht1 hlo'.le hm0
    rwa [Real.rpow_inv_natCast_pow hlo.le hm0] at h
  have htm2 : (t : ℝ) ^ m < β / N := by
    have h := pow_lt_pow_left₀ ht2 htpos.le hm0
    rwa [Real.rpow_inv_natCast_pow (hlo.le.trans hlohi.le) hm0] at h

  have hna : ‖((t : ℚ) : w₀.Completion)‖ = t := by
    rw [norm_ratCast_completion, abs_of_pos htpos]
  have ha0 : ((t : ℚ) : w₀.Completion) ≠ 0 := norm_pos_iff.mp (by rw [hna]; exact htpos)
  refine ⟨archCentralUnit F w₀ (Units.mk0 _ ha0), ?_⟩
  have hdet : ideleNorm F (Matrix.GeneralLinearGroup.det
      (centralScalar (𝓞 F) F (archCentralUnit F w₀ (Units.mk0 _ ha0)) * g)) = (t : ℝ) ^ m * N := by
    rw [map_mul, ideleNorm_mul, ideleNorm_det_centralScalar_archCentralUnit, Units.val_mk0, hna, hm, pow_mul, sq]
  rw [hdet]
  exact ⟨(div_lt_iff₀ hN).mp htm1, (lt_div_iff₀ hN).mp htm2⟩

section Apply

variable {c₀ u₀ e₁ e₂ : ℝ} {T₀ : Finset (AdelicGL2 (𝓞 F) F)}

theorem apply_mul_eq_of_peterssonIntegral_sub_self_eq_zero
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (wpins F c₀ u₀ e₁ e₂ T₀) Φ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F (wpins F c₀ u₀ e₁ e₂ T₀) Φ.toRawCentral R)
    (s α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hcovV : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) →
      peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
          peterssonIntegral F s S x y)
    (hP0 : peterssonIntegral F s S R.toFun R.toFun ≠ 0)
    (h₁ h₂ : AdelicGL2 (𝓞 F) F)
    (hnull : peterssonIntegral F s S (fun z => R.toFun (z * h₁) - R.toFun (z * h₂))
      (fun z => R.toFun (z * h₁) - R.toFun (z * h₂)) = 0) :
    ∀ g : AdelicGL2 (𝓞 F) F, R.toFun (g * h₁) = R.toFun (g * h₂) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have _ := hSs

  have hcont : Continuous R.toFun := hR
  have hls := ((lsXiMemberAt_iff _ _ _ _ _ _ _).mp R.smoothCusp.1.1).1
  have hl : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      R.toFun (globalPoints (𝓞 F) F γ * g) = R.toFun g := hls.left_invariant
  set ω : (AdeleRing (𝓞 F) F)ˣ → ℂ := fun z => ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) with hω
  have hz : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      R.toFun (centralScalar (𝓞 F) F z * g) = ω z * R.toFun g :=
    fun z g => hls.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hωne : ∀ z, ω z ≠ 0 := fun z => Units.ne_zero _

  have hmem : ∀ h : AdelicGL2 (𝓞 F) F, (fun z => R.toFun (z * h)) ∈
      Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) :=
    fun h => Submodule.subset_span ⟨h, rfl⟩
  set x : AdelicGL2 (𝓞 F) F → ℂ := fun z => R.toFun (z * h₁) - R.toFun (z * h₂) with hxdef
  have hxmem : x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) := by
    have := Submodule.sub_mem _ (hmem h₁) (hmem h₂)
    exact this
  obtain ⟨hxc, hxl, hxz⟩ := span_props hcont hl hz hxmem

  have hself : (fun z : AdelicGL2 (𝓞 F) F => R.toFun (z * 1)) = R.toFun := by
    funext z; rw [mul_one]
  have hmem0 : R.toFun ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R.toFun (z * h)) :=
    Submodule.subset_span ⟨1, hself⟩
  have hPne : ∀ h : AdelicGL2 (𝓞 F) F,
      peterssonIntegral F s S (fun z => R.toFun (z * h)) (fun z => R.toFun (z * h)) ≠ 0 := by
    intro h
    have hc := hcovV h R.toFun R.toFun hmem0 hmem0
    rw [hc]
    exact mul_ne_zero (by exact_mod_cast (Real.rpow_pos_of_pos (ideleNorm_pos _) s).ne') hP0
  have hi₁ := integrable_normSq_weight_of_petersson_self_ne_zero (hPne h₁)
  have hi₂ := integrable_normSq_weight_of_petersson_self_ne_zero (hPne h₂)
  have hint := integrable_integrand_sub (s := s) (S := S)
    (hcont.comp (continuous_id.mul continuous_const)) (hcont.comp (continuous_id.mul continuous_const)) hi₁ hi₂

  have hae : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S), x g = 0 :=
    ae_eq_zero_of_petersson_self_eq_zero hint hnull

  set A : Set (AdelicGL2 (𝓞 F) F) := {g | x g ≠ 0} with hAdef
  have hAopen : IsOpen A := isOpen_ne_fun hxc continuous_const
  have hA0 : ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) A = 0 := by
    rw [← compl_mem_ae_iff]
    filter_upwards [hae] with g hg
    simp only [hAdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
    exact hg
  have hinv : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), globalPoints (𝓞 F) F γ * g ∈ A ↔ g ∈ A := by
    intro γ g
    simp only [hAdef, Set.mem_setOf_eq, hxl]
  have hslab := measure_inter_slab_eq_zero hS hAopen.measurableSet hinv hA0

  set O : Set (AdelicGL2 (𝓞 F) F) := A ∩ {g | α < ideleNorm F (Matrix.GeneralLinearGroup.det g) ∧
      ideleNorm F (Matrix.GeneralLinearGroup.det g) < β} with hOdef
  have hOopen : IsOpen O :=
    hAopen.inter ((isOpen_lt continuous_const (continuous_ideleNorm_det F)).inter
      (isOpen_lt (continuous_ideleNorm_det F) continuous_const))
  have hOnull : (adelicGLHaar (Fin 2) (𝓞 F) F) O = 0 := by
    refine le_antisymm ((measure_mono ?_).trans hslab.le) zero_le
    rintro g ⟨hgA, hg1, hg2⟩
    exact ⟨hgA, hg1.le, hg2.le⟩
  have hOempty : O = ∅ := hOopen.eq_empty_of_measure_zero hOnull

  intro g
  obtain ⟨z, hz1, hz2⟩ := exists_centralScalar_mul_mem_openSlab hα hαβ g
  have hzg : centralScalar (𝓞 F) F z * g ∉ A := by
    intro hmemA
    have : centralScalar (𝓞 F) F z * g ∈ O := ⟨hmemA, hz1, hz2⟩
    rw [hOempty] at this
    exact this
  have hx0 : x (centralScalar (𝓞 F) F z * g) = 0 := by
    simp only [hAdef, Set.mem_setOf_eq, not_not] at hzg
    exact hzg
  rw [hxz] at hx0
  have hxg : x g = 0 := (mul_eq_zero.mp hx0).resolve_left (hωne z)
  exact sub_eq_zero.mp hxg

end Apply

end AutomorphicForm.PeterssonHeckeBoundGeneralAux.Rigidity

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsGenuineCuspRealizationAt IsArithGenuineCuspRealizable CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff HeckeEigensystem.cNorm HeckeEigensystem.toRawCentral_b SmoothCuspRealizationAt HeckeEigensystem SiegelCovering.CoversModCentre SiegelCovering.glFin_centralScalar_archCentralUnit peterssonIntegral exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine ideleNorm_det_globalPoints SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt"
namespace PeterssonHeckeBoundGeneralAux
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

section Bound

variable {c₀ u₀ e₁ e₂ : ℝ} {T₀ : Finset (AdelicGL2 (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ}
  (D : PairingData F c₀ u₀ e₁ e₂ T₀ Φ)

noncomputable def levelPrimes (Φ : HeckeEigensystem F ℂ) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Ideal.finite_factors (I := Φ.level) (by rw [Ne, Ideal.zero_eq_bot]; exact Φ.level_ne_bot)).toFinset

theorem not_dvd_level_of_not_mem_levelPrimes {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ levelPrimes Φ) :
    ¬ v.asIdeal ∣ Φ.level := fun h => hv ((Set.Finite.mem_toFinset _).mpr h)

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h

theorem norm_cNorm (v : HeightOneSpectrum (𝓞 F)) :
    ‖HeckeEigensystem.cNorm v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  simp [HeckeEigensystem.cNorm]

theorem normSq_a_lt {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ D.R.exceptionalSet) (hlev : ¬ v.asIdeal ∣ Φ.level) :
    Complex.normSq (Φ.a v) < ((Ideal.absNorm v.asIdeal + 1 : ℕ) : ℝ) ^ 2 * ‖Φ.toRawCentral.b v‖ := by
  obtain ⟨reps, hsys, heig, hle, heq⟩ := normSq_a_le_and_eq_case D hv
  refine lt_of_le_of_ne hle fun hE => ?_
  have hnull := heq hE
  have hpt : ∀ i j, ∀ g : AdelicGL2 (𝓞 F) F, D.R.toFun (g * reps i) = D.R.toFun (g * reps j) := fun i j =>
    AutomorphicForm.PeterssonHeckeBoundGeneralAux.Rigidity.apply_mul_eq_of_peterssonIntegral_sub_self_eq_zero Φ D.R D.hR D.s 1 2 one_pos one_lt_two D.S D.hSs
      D.hS D.covInt D.intNe (reps i) (reps j) (hnull i j)
  obtain ⟨cst, hcst⟩ := exists_forall_doubleCoset_of_tr_eq D hsys heig hpt
  refine AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt
    F (⋃ x ∈ T₀, (· * x) '' centreCutSiegelSet F c₀ u₀ e₁ e₂)
    Φ.toRawCentral D.R D.hR v hlev ⟨cst, fun g => ?_⟩
  exact hcst _ (HeckePair.self_mem_doubleCoset _) g

end Bound

end AutomorphicForm.PeterssonHeckeBoundGeneralAux

end

p2m_open "IsDedekindDomain NumberField AutomorphicForm P2MW.S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable_of_coversModCentre.AutomorphicForm"
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel
open AutomorphicForm.PeterssonHeckeBoundGeneralAux in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : AutomorphicForm.SiegelCovering.CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Φ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
        (∃ t : ℝ, 0 ≤ t ∧ Φ.a v ^ 2 = (t : ℂ) * Φ.b v) ∧
        ‖Φ.a v‖ ^ 2 <
          ‖Φ.b v‖ * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) := by
  classical
  have _ := hc
  have _ := hd₁
  obtain ⟨D⟩ := nonempty_pairingData hd hcov Φ hΦ
  refine ⟨D.R.exceptionalSet ∪ levelPrimes Φ, fun p hp => ?_⟩
  have hexc : p ∉ D.R.exceptionalSet := fun h => hp (Finset.mem_union_left _ h)
  have hlev : ¬ p.asIdeal ∣ Φ.level :=
    not_dvd_level_of_not_mem_levelPrimes fun h => hp (Finset.mem_union_right _ h)
  have hN : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℕ) := absNorm_pos p
  have hF3 := centralScalar_det_gen_mul_inv_mem_doubleCoset (F := F) Φ.level_ne_bot hlev
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

end S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable_of_coversModCentre
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable_of_coversModCentre (solution)
