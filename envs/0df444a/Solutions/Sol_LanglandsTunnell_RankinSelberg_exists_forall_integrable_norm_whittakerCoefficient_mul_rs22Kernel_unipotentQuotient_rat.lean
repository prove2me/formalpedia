-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/26b5609d-bdbc-5bad-a47d-7e578f34736c

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar
import Theorems.Thm_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat
import Theorems.Thm_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat
import Theorems.Thm_LanglandsTunnell_Converse_exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure
import Theorems.Thm_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm LanglandsTunnell RSCarrier
open NumberField.AdelicLevel
open scoped ENNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

set_option autoImplicit false

namespace ArchFiniteFactorisation

section Generic

private theorem sigmaCompactSpace_mulOpposite {M : Type*} [TopologicalSpace M] [SigmaCompactSpace M] :
    SigmaCompactSpace Mᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace

private theorem sigmaCompactSpace_units {M : Type*} [Monoid M] [TopologicalSpace M] [T1Space M] [ContinuousMul M]
    [SigmaCompactSpace M] : SigmaCompactSpace Mˣ :=
  haveI := sigmaCompactSpace_mulOpposite (M := M)
  Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

private theorem sigmaCompactSpace_matrix {A : Type*} [TopologicalSpace A] [SigmaCompactSpace A] :
    SigmaCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
  inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → A))

private theorem sigmaCompactSpace_generalLinearGroup {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A]
    [T2Space A] [SigmaCompactSpace A] : SigmaCompactSpace (GL (Fin 2) A) :=
  haveI := sigmaCompactSpace_matrix (A := A)
  sigmaCompactSpace_units

private theorem sigmaCompactSpace_of_isClosed {G : Type*} [Group G] [TopologicalSpace G] [SigmaCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : SigmaCompactSpace H :=
  hH.sigmaCompactSpace

private theorem sigmaFinite_of_isHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] (μ : Measure G) [μ.IsHaarMeasure] : SigmaFinite μ :=
  inferInstance

end Generic

section Adelic

private scoped instance sigmaCompactSpace_gl_real : SigmaCompactSpace (GL (Fin 2) ℝ) :=
  sigmaCompactSpace_generalLinearGroup

private scoped instance sigmaCompactSpace_adelicGL2 : SigmaCompactSpace (AdelicGL2 (𝓞 ℚ) ℚ) :=
  sigmaCompactSpace_generalLinearGroup

private scoped instance sigmaCompactSpace_finiteAdelicGL2Subgroup : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) :=
  sigmaCompactSpace_of_isClosed _ (isClosed_finiteAdelicGL2Subgroup ℚ)

attribute [local instance] AdelicHaar.glBorel

private theorem sigmaFinite_adelicGLHaar : SigmaFinite (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  sigmaFinite_of_isHaarMeasure _

end Adelic

end ArchFiniteFactorisation
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

namespace ArchFiniteFactorisation

private theorem isReal_default : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal default

section SectionLaws

private theorem archRealGLAt_ratArchGL2_mul_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archRealGLAt isReal_default (ratArchGL2 g) * (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = g :=
  mul_inv_cancel_left _ _

private theorem glArch_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) : glArch (𝓞 ℚ) ℚ (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).mp (finFactor g).2

private theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) : glFin (𝓞 ℚ) ℚ (archRealGLAt isReal_default m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

private theorem glFin_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glFin (𝓞 ℚ) ℚ (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = glFin (𝓞 ℚ) ℚ g := by
  show glFin (𝓞 ℚ) ℚ ((archRealGLAt isReal_default (ratArchGL2 g))⁻¹ * g) = _
  rw [map_mul, map_inv, glFin_archRealGLAt, inv_one, one_mul]

end SectionLaws
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

section RealComponent

private theorem ratArchGL2_mul (g g' : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (g * g') = ratArchGL2 g * ratArchGL2 g' := by
  unfold ratArchGL2
  simp only [map_mul]

private theorem ratArchGL2_one : ratArchGL2 1 = 1 := by
  unfold ratArchGL2
  simp only [map_one]

private theorem ratArchGL2_eq_archRealProjAt (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ratArchGL2 g = archRealProjAt isReal_default g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem ratArchGL2_archRealGLAt (m : GL (Fin 2) ℝ) : ratArchGL2 (archRealGLAt isReal_default m) = m := by
  rw [ratArchGL2_eq_archRealProjAt]
  exact archRealProjAt_archRealGLAt _ m

private theorem ratArchGL2_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  unfold ratArchGL2
  rw [glArch_finFactor, map_one, map_one]

end RealComponent
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

section HomLaws

private theorem finFactor_coe (k : finiteAdelicGL2Subgroup ℚ) : finFactor (k : AdelicGL2 (𝓞 ℚ) ℚ) = k := by
  apply Subtype.ext
  show (archRealGLAt isReal_default (ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹ * (k : AdelicGL2 (𝓞 ℚ) ℚ) = k
  have hk : ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    unfold ratArchGL2
    rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).mp k.2, map_one, map_one]
  rw [hk, map_one, inv_one, one_mul]

private theorem finFactor_one : finFactor 1 = 1 := by
  apply Subtype.ext
  show (archRealGLAt isReal_default (ratArchGL2 1))⁻¹ * 1 = 1
  rw [ratArchGL2_one, map_one, inv_one, mul_one]

private theorem finFactor_mul (g g' : AdelicGL2 (𝓞 ℚ) ℚ) : finFactor (g * g') = finFactor g * finFactor g' := by
  apply Subtype.ext
  have hcomm := archRealGLAt_mul_comm_of_glArch_eq_one isReal_default (ratArchGL2 g')⁻¹ (glArch_finFactor g)
  rw [map_inv] at hcomm
  show (archRealGLAt isReal_default (ratArchGL2 (g * g')))⁻¹ * (g * g') =
    (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) * (finFactor g' : AdelicGL2 (𝓞 ℚ) ℚ)
  rw [ratArchGL2_mul, map_mul, mul_inv_rev]
  calc (archRealGLAt isReal_default (ratArchGL2 g'))⁻¹ * (archRealGLAt isReal_default (ratArchGL2 g))⁻¹ * (g * g')
      = (archRealGLAt isReal_default (ratArchGL2 g'))⁻¹ * (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) * g' := by
        show _ = _ * ((archRealGLAt isReal_default (ratArchGL2 g))⁻¹ * g) * g'
        simp only [mul_assoc]
    _ = (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) * (archRealGLAt isReal_default (ratArchGL2 g'))⁻¹ * g' := by
        rw [hcomm]
    _ = (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) * (finFactor g' : AdelicGL2 (𝓞 ℚ) ℚ) := by
        show _ = _ * ((archRealGLAt isReal_default (ratArchGL2 g'))⁻¹ * g')
        rw [mul_assoc]

end HomLaws
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

end ArchFiniteFactorisation
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

namespace ArchFiniteFactorisation

section ComponentIso

open NumberField.InfinitePlace.Completion

private theorem continuous_generalLinearGroup_map {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f))

private theorem continuous_ringEquivRealOfIsReal : Continuous (ringEquivRealOfIsReal isReal_default) := by
  have h : (fun x => ringEquivRealOfIsReal isReal_default x) = isometryEquivRealOfIsReal isReal_default := rfl
  show Continuous fun x => ringEquivRealOfIsReal isReal_default x
  rw [h]
  exact (isometryEquivRealOfIsReal isReal_default).continuous

private theorem continuous_ringEquivRealOfIsReal_symm : Continuous (ringEquivRealOfIsReal isReal_default).symm := by
  have h : (fun r => (ringEquivRealOfIsReal isReal_default).symm r)
      = (isometryEquivRealOfIsReal isReal_default).symm := rfl
  show Continuous fun r => (ringEquivRealOfIsReal isReal_default).symm r
  rw [h]
  exact (isometryEquivRealOfIsReal isReal_default).symm.continuous

private theorem continuous_ratArchGL2 : Continuous ratArchGL2 := by
  unfold ratArchGL2
  exact (continuous_generalLinearGroup_map _ continuous_ringEquivRealOfIsReal).comp
    ((continuous_archComponent ℚ default).comp (continuous_glArch (𝓞 ℚ) ℚ))

private theorem continuous_glEquivOfRingEquiv {A B : Type*} [NormedField A] [NormedField B] (e : A ≃+* B)
    (he : Continuous e) : Continuous (glEquivOfRingEquiv e) := by
  unfold glEquivOfRingEquiv
  exact Continuous.units_map (RingEquiv.mapMatrix (m := Fin 2) e).toMulEquiv.toMonoidHom
    ((continuous_id.matrix_map he : Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map e))

private theorem continuous_archMatrixUpdate (w : InfinitePlace ℚ) : Continuous (archMatrixUpdate ℚ w) := by
  refine continuous_matrix fun i j => continuous_pi fun w' => ?_
  show Continuous fun m : Matrix (Fin 2) (Fin 2) w.Completion => archMatrixPiEquiv ℚ (archMatrixUpdate ℚ w m) w' i j
  simp_rw [archMatrixPiEquiv_archMatrixUpdate]
  obtain rfl : w' = w := Subsingleton.elim w' w
  simp only [Function.update_self]
  exact continuous_id.matrix_elem i j

private theorem continuous_archGLIncl (w : InfinitePlace ℚ) : Continuous (archGLIncl ℚ w) := by
  unfold archGLIncl
  exact Continuous.units_map _ (continuous_archMatrixUpdate w)

private theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl ℚ) := by
  have h₁ : Continuous fun p : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) ×
      Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) => (adelicMatrixProdEquiv ℚ).symm p :=
    continuous_matrix fun i j => (continuous_fst.matrix_elem i j).prodMk (continuous_snd.matrix_elem i j)
  have h₂ : Continuous (Units.mapEquiv (adelicMatrixProdEquiv ℚ).symm.toMulEquiv) :=
    Continuous.units_map (adelicMatrixProdEquiv ℚ).symm.toMulEquiv.toMonoidHom h₁
  have h₃ : Continuous (MulEquiv.prodUnits.symm : GL (Fin 2) (InfiniteAdeleRing ℚ) ×
      GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) → _) :=
    (Homeomorph.prodUnits (α := Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))
      (β := Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))).symm.continuous
  unfold adelicArchGLIncl
  exact h₂.comp (h₃.comp (continuous_id.prodMk continuous_const))

private theorem continuous_archRealGLAt : Continuous (archRealGLAt (F := ℚ) isReal_default) :=
  continuous_adelicArchGLIncl.comp ((continuous_archGLIncl default).comp
    (continuous_glEquivOfRingEquiv _ continuous_ringEquivRealOfIsReal_symm))

private theorem continuous_coe_finFactor : Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) :=
  ((continuous_archRealGLAt.comp continuous_ratArchGL2).inv).mul continuous_id

private theorem continuous_finFactor : Continuous finFactor :=
  continuous_coe_finFactor.subtype_mk fun g => (finFactor g).2

private theorem ratArchGL2_coe (k : finiteAdelicGL2Subgroup ℚ) : ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  unfold ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).mp k.2, map_one, map_one]

private theorem finFactor_archRealGLAt (m : GL (Fin 2) ℝ) : finFactor (archRealGLAt isReal_default m) = 1 := by
  apply Subtype.ext
  show (archRealGLAt isReal_default (ratArchGL2 (archRealGLAt isReal_default m)))⁻¹ *
    archRealGLAt isReal_default m = 1
  rw [ratArchGL2_archRealGLAt, inv_mul_cancel]

private noncomputable def componentIso : AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ* GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ where
  toFun g := (ratArchGL2 g, finFactor g)
  invFun p := archRealGLAt isReal_default p.1 * (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)
  left_inv g := archRealGLAt_ratArchGL2_mul_finFactor g
  right_inv p := by
    obtain ⟨m, k⟩ := p
    refine Prod.ext ?_ ?_
    · show ratArchGL2 (archRealGLAt isReal_default m * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = m
      rw [ratArchGL2_mul, ratArchGL2_archRealGLAt, ratArchGL2_coe, mul_one]
    · show finFactor (archRealGLAt isReal_default m * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = k
      rw [finFactor_mul, finFactor_archRealGLAt, finFactor_coe, one_mul]
  map_mul' g g' := Prod.ext (ratArchGL2_mul g g') (finFactor_mul g g')
  continuous_toFun := continuous_ratArchGL2.prodMk continuous_finFactor
  continuous_invFun :=
    (continuous_archRealGLAt.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

private theorem componentIso_apply (g : AdelicGL2 (𝓞 ℚ) ℚ) : componentIso g = (ratArchGL2 g, finFactor g) := rfl

end ComponentIso
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

end ArchFiniteFactorisation
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

namespace ArchFiniteFactorisation

open Topology

section Legs
variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]

omit [TopologicalSpace R] [T2Space R] in

private theorem coe_range_unipotentGL2Hom :
    ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) =
      {g : GL (Fin 2) R | Units.val g 0 0 = 1 ∧ Units.val g 1 0 = 0 ∧ Units.val g 1 1 = 1} := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    change Units.val (unipotentGL2 y.toAdd) 0 0 = 1 ∧ Units.val (unipotentGL2 y.toAdd) 1 0 = 0 ∧
      Units.val (unipotentGL2 y.toAdd) 1 1 = 1
    simp [unipotentGL2]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd (Units.val g 0 1), ?_⟩
    change unipotentGL2 (Units.val g 0 1) = g
    refine Units.ext ?_
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

private theorem isClosed_range_unipotentGL2Hom :
    IsClosed ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) := by
  rw [coe_range_unipotentGL2Hom]
  have hc : Continuous fun g : GL (Fin 2) R => Units.val g := Units.continuous_val
  exact (isClosed_eq (hc.matrix_elem 0 0) continuous_const).inter
    ((isClosed_eq (hc.matrix_elem 1 0) continuous_const).inter
      (isClosed_eq (hc.matrix_elem 1 1) continuous_const))

private theorem locallyCompactSpace_of_isClosed {G : Type*} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : LocallyCompactSpace H :=
  hH.locallyCompactSpace

private theorem locallyCompactSpace_gl_real : LocallyCompactSpace (GL (Fin 2) ℝ) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : Matrix (Fin 2) (Fin 2) ℝ ≃ₜ
      (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ).symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

private theorem locallyCompactSpace_generalLinearGroup {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] : LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : Matrix (Fin 2) (Fin 2) A ≃ₜ
      (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ).symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

private theorem isMulRightInvariant_of_comm {H : Type*} [Group H] [MeasurableSpace H] (μ : Measure H)
    [μ.IsMulLeftInvariant] (hcomm : ∀ a b : H, a * b = b * a) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : (fun x : H => x * g) = fun x : H => g * x := funext fun x => hcomm x g
  rw [h]
  exact map_mul_left_eq_self μ g

private theorem range_mul_comm {M G : Type*} [CommGroup M] [Group G] (φ : M →* G) (a b : φ.range) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

private theorem subgroupOf_mul_comm {G : Type*} [Group G] (H K : Subgroup G) (hcomm : ∀ a b : H, a * b = b * a)
    (a b : H.subgroupOf K) : a * b = b * a := by
  apply Subtype.ext
  apply Subtype.ext
  have ha : ((a : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp a.2
  have hb : ((b : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp b.2
  have := congrArg Subtype.val (hcomm ⟨_, ha⟩ ⟨_, hb⟩)
  simpa using this

private theorem map_prodMap_prod {X₁ X₂ Y₁ Y₂ : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y₁]
    [MeasurableSpace Y₂] (μ₁ : Measure X₁) (μ₂ : Measure X₂) [SFinite μ₁] [SFinite μ₂] {f : X₁ → Y₁}
    {g : X₂ → Y₂} (hf : Measurable f) (hg : Measurable g) :
    (μ₁.prod μ₂).map (Prod.map f g) = (μ₁.map f).prod (μ₂.map g) :=
  (Measure.map_prod_map μ₁ μ₂ hf hg).symm

end Legs
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

private theorem isClosed_subgroupOf {A : Type*} [Group A] [TopologicalSpace A] (H K : Subgroup A)
    (hH : IsClosed (H : Set A)) : IsClosed ((H.subgroupOf K : Subgroup K) : Set K) := by
  rw [Subgroup.coe_subgroupOf]
  exact hH.preimage continuous_subtype_val

section LC
variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

private theorem secondCountableTopology_op {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] :
    SecondCountableTopology Xᵐᵒᵖ :=
  (MulOpposite.opHomeomorph : X ≃ₜ Xᵐᵒᵖ).symm.isInducing.secondCountableTopology

omit [IsTopologicalRing A] in

private theorem secondCountableTopology_generalLinearGroup [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) :=
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ := secondCountableTopology_op
  Units.isInducing_embedProduct.secondCountableTopology

end LC
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

section Core
variable {G : Type*} [Group G] (H : Subgroup G)

local notation "Q" => MulAction.orbitRel.Quotient H G

private theorem mk_mul_eq (x : H) (g : G) :
    (Quotient.mk'' ((x : G) * g) : Q) = Quotient.mk'' g :=
  Quotient.sound' (MulAction.mem_orbit g x)

private theorem mk_out (q : Q) : (Quotient.mk'' q.out : Q) = q := Quotient.out_eq' q

private theorem exists_mul_eq_of_mk_eq {g g' : G} (h : (Quotient.mk'' g : Q) = Quotient.mk'' g') :
    ∃ x : H, (x : G) * g' = g := by
  have h' : (MulAction.orbitRel H G) g g' := Quotient.exact' h
  obtain ⟨x, hx⟩ := (MulAction.orbitRel_apply).1 h'
  exact ⟨x, hx⟩

variable {H} [MeasurableSpace G]

private theorem map_withDensity_comp' {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) {Θ : X → Y}
    (hΘ : Measurable Θ) {ρ : Y → ℝ≥0∞} (hρ : Measurable ρ) :
    (μ.withDensity fun x => ρ (Θ x)).map Θ = (μ.map Θ).withDensity ρ := by
  ext S hS
  rw [Measure.map_apply hΘ hS, withDensity_apply _ (hΘ hS), withDensity_apply _ hS,
    setLIntegral_map hS hρ hΘ]

private theorem map_withDensity_eq_of_unfolding (μ : Measure G) (μH : Measure H) (ν : Measure Q)
    (hunf : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ g, F g ∂μ = ∫⁻ q, (∫⁻ x : H, F ((x : G) * q.out) ∂μH) ∂ν)
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρ1 : ∀ g, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1) :
    (μ.withDensity ρ).map (Quotient.mk'' : G → Q) = ν := by
  ext S hS
  have hpre : MeasurableSet ((Quotient.mk'' : G → Q) ⁻¹' S) := measurable_quotient_mk'' hS
  rw [Measure.map_apply measurable_quotient_mk'' hS, withDensity_apply _ hpre,
    ← lintegral_indicator hpre]
  have hF : Measurable (((Quotient.mk'' : G → Q) ⁻¹' S).indicator ρ) := hρ.indicator hpre
  rw [hunf _ hF]
  have hinner : ∀ q : Q, (∫⁻ x : H, ((Quotient.mk'' : G → Q) ⁻¹' S).indicator ρ ((x : G) * q.out) ∂μH) =
      S.indicator (fun _ => (1 : ℝ≥0∞)) q := by
    intro q
    by_cases hq : q ∈ S
    · have hmem : ∀ x : H, (x : G) * q.out ∈ (Quotient.mk'' : G → Q) ⁻¹' S := by
        intro x
        show (Quotient.mk'' ((x : G) * q.out) : Q) ∈ S
        rw [mk_mul_eq H x q.out, mk_out H q]
        exact hq
      simp only [Set.indicator_of_mem (hmem _), Set.indicator_of_mem hq]
      exact hρ1 _
    · have hmem : ∀ x : H, (x : G) * q.out ∉ (Quotient.mk'' : G → Q) ⁻¹' S := by
        intro x hx
        apply hq
        have hx' : (Quotient.mk'' ((x : G) * q.out) : Q) ∈ S := hx
        rwa [mk_mul_eq H x q.out, mk_out H q] at hx'
      simp only [Set.indicator_of_notMem (hmem _), Set.indicator_of_notMem hq, lintegral_zero]
  simp only [hinner]
  rw [lintegral_indicator hS, setLIntegral_one]

private theorem integral_comp_section_map_mk (ν : Measure G) {f : G → ℂ} (hf : Measurable f) {σ : Q → G}
    (hsec : ∀ g, f (σ (Quotient.mk'' g)) = f g) :
    ∫ q, f (σ q) ∂(ν.map (Quotient.mk'' : G → Q)) = ∫ g, f g ∂ν := by
  have hfσ : Measurable (fun q : Q => f (σ q)) := by
    refine measurable_from_quotient.2 ?_
    have : ((fun q : Q => f (σ q)) ∘ (Quotient.mk'' : G → Q)) = f := by
      funext g
      exact hsec g
    rw [this]
    exact hf
  rw [integral_map measurable_quotient_mk''.aemeasurable hfσ.aestronglyMeasurable]
  simp only [hsec]

omit [MeasurableSpace G] in

private theorem section_eq_of_invariant {f : G → ℂ} (hinv : ∀ (x : H) (g : G), f ((x : G) * g) = f g) {σ : Q → G}
    (hσ : ∀ q : Q, (Quotient.mk'' (σ q) : Q) = q) (g : G) : f (σ (Quotient.mk'' g)) = f g := by
  obtain ⟨x, hx⟩ := exists_mul_eq_of_mk_eq H (hσ (Quotient.mk'' g))
  rw [← hx, hinv]

omit [Group G] in

private theorem integral_withDensity_mul_comp_eq_mul {A₁ A₂ : Type*} [MeasurableSpace A₁] [MeasurableSpace A₂]
    (μ : Measure G) {Θ : G → A₁ × A₂} (hΘ : Measurable Θ) (μ₁ : Measure A₁) (μ₂ : Measure A₂) [SFinite μ₁]
    [SFinite μ₂] (hsplit : μ.map Θ = μ₁.prod μ₂) {ρ₁ : A₁ → ℝ≥0∞} {ρ₂ : A₂ → ℝ≥0∞} (h₁ : Measurable ρ₁)
    (h₂ : Measurable ρ₂) (F₁ : A₁ → ℂ) (F₂ : A₂ → ℂ)
    (hint : Integrable (fun p : A₁ × A₂ => F₁ p.1 * F₂ p.2) ((μ₁.withDensity ρ₁).prod (μ₂.withDensity ρ₂))) :
    ∫ g, F₁ (Θ g).1 * F₂ (Θ g).2 ∂(μ.withDensity fun g => ρ₁ (Θ g).1 * ρ₂ (Θ g).2) =
      (∫ a, F₁ a ∂(μ₁.withDensity ρ₁)) * ∫ b, F₂ b ∂(μ₂.withDensity ρ₂) := by
  have hρ : Measurable fun p : A₁ × A₂ => ρ₁ p.1 * ρ₂ p.2 := (h₁.comp measurable_fst).mul (h₂.comp measurable_snd)
  have hmap : (μ.withDensity fun g => ρ₁ (Θ g).1 * ρ₂ (Θ g).2).map Θ =
      (μ₁.withDensity ρ₁).prod (μ₂.withDensity ρ₂) := by
    have h := map_withDensity_comp' μ hΘ hρ
    rw [hsplit, ← prod_withDensity₀ h₁.aemeasurable h₂.aemeasurable] at h
    exact h
  have hF : AEStronglyMeasurable (fun p : A₁ × A₂ => F₁ p.1 * F₂ p.2)
      ((μ.withDensity fun g => ρ₁ (Θ g).1 * ρ₂ (Θ g).2).map Θ) := by
    rw [hmap]
    exact hint.aestronglyMeasurable
  have h := integral_map (μ := μ.withDensity fun g => ρ₁ (Θ g).1 * ρ₂ (Θ g).2)
    (f := fun p : A₁ × A₂ => F₁ p.1 * F₂ p.2) hΘ.aemeasurable hF
  rw [hmap] at h
  exact h.symm.trans (integral_prod_mul F₁ F₂)

end Core
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

section Normalisation

private theorem lintegral_mul_comp_eq_one {N G₁ G₂ : Type*} [MeasurableSpace N] [MeasurableSpace G₁]
    [MeasurableSpace G₂]
    (ν : Measure N) (m₁ : Measure G₁) (m₂ : Measure G₂) [SFinite m₁] [SFinite m₂] {Θ : N → G₁ × G₂}
    (hΘ : Measurable Θ) (hsplit : ν.map Θ = m₁.prod m₂) {F₁ : G₁ → ENNReal} {F₂ : G₂ → ENNReal}
    (h₁ : Measurable F₁) (h₂ : Measurable F₂) (n₁ : ∫⁻ x, F₁ x ∂m₁ = 1) (n₂ : ∫⁻ y, F₂ y ∂m₂ = 1) :
    ∫⁻ n, F₁ (Θ n).1 * F₂ (Θ n).2 ∂ν = 1 := by
  have hG : Measurable fun p : G₁ × G₂ => F₁ p.1 * F₂ p.2 := (h₁.comp measurable_fst).mul (h₂.comp measurable_snd)
  calc ∫⁻ n, F₁ (Θ n).1 * F₂ (Θ n).2 ∂ν = ∫⁻ p, F₁ p.1 * F₂ p.2 ∂(ν.map Θ) := (lintegral_map hG hΘ).symm
    _ = ∫⁻ p, F₁ p.1 * F₂ p.2 ∂(m₁.prod m₂) := by rw [hsplit]
    _ = 1 := by rw [lintegral_prod_mul h₁.aemeasurable h₂.aemeasurable, n₁, n₂, one_mul]

private theorem lintegral_map_val_mul_eq_one {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (μ : Measure H) {ρ : G → ENNReal} (hρ : Measurable ρ) (a : G)
    (hμ : ∫⁻ h : H, ρ ((h : G) * a) ∂μ = 1) : ∫⁻ x, ρ (x * a) ∂(μ.map (Subtype.val : H → G)) = 1 := by
  have h := lintegral_map (μ := μ) (f := fun x : G => ρ (x * a)) (hρ.comp (measurable_mul_const a))
    (measurable_subtype_coe : Measurable (Subtype.val : H → G))
  exact h.trans hμ

end Normalisation
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

section DensNorm

open HaarQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SigmaCompactSpace G] [WeaklyLocallyCompactSpace G]
  (H : Subgroup G) (μH : Measure H)

private def coeff (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ n *
    (1 + μH (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹

omit [IsTopologicalGroup G] [BorelSpace G] in
private theorem weight_eq (g : G) :
    weight H μH g = ∑' n : ℕ,
      coeff H μH n * (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g := by
  unfold HaarQuotient.weight
  rw [dif_pos ⟨inferInstance, inferInstance⟩]
  rfl

omit [IsTopologicalGroup G] [BorelSpace G] in
private theorem coeff_le (n : ℕ) : coeff H μH n ≤ (2⁻¹ : ℝ≥0∞) ^ n :=
  mul_le_of_le_one_right (by simp) (ENNReal.inv_le_one.mpr le_self_add)

private theorem lintegral_term_le [μH.IsMulRightInvariant] (n : ℕ) (g : G) :
    ∫⁻ x : H, coeff H μH n *
        (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) ∂μH ≤
      (2⁻¹ : ℝ≥0∞) ^ n := by
  set E : Set G := CompactExhaustion.choice G (n + 1) with hE
  set U : Set H := {x : H | (x : G) * g ∈ interior E} with hU
  have hUmeas : MeasurableSet U :=
    (isOpen_interior.preimage (continuous_subtype_val.mul continuous_const)).measurableSet
  have hfun : (fun x : H => coeff H μH n * (interior E).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g)) =
      fun x : H => U.indicator (fun _ => coeff H μH n) x := by
    funext x
    by_cases hx : x ∈ U
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (show (x : G) * g ∈ interior E from hx)]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (x : G) * g ∉ interior E from hx)]
  rw [hfun, lintegral_indicator_const hUmeas]

  by_cases hne : U = ∅
  · simp [hne]
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hsub : U ⊆ (fun x : H => x * x₀⁻¹) ⁻¹' (((↑) : H → G) ⁻¹' (E * E⁻¹)) := by
    intro x hx
    refine ⟨(x : G) * g, interior_subset hx, ((x₀ : G) * g)⁻¹, Set.inv_mem_inv.mpr (interior_subset hx₀), ?_⟩
    simp [mul_assoc]
  calc coeff H μH n * μH U ≤ coeff H μH n * μH ((fun x : H => x * x₀⁻¹) ⁻¹' (((↑) : H → G) ⁻¹' (E * E⁻¹))) :=
        mul_le_mul_right (measure_mono hsub) _
    _ = coeff H μH n * μH (((↑) : H → G) ⁻¹' (E * E⁻¹)) := by rw [measure_preimage_mul_right]
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
        unfold coeff
        rw [mul_assoc]
        refine mul_le_of_le_one_right (by simp) ?_
        rw [← hE, ← ENNReal.div_eq_inv_mul]
        exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)

private theorem measurable_term (n : ℕ) (g : G) :
    Measurable fun x : H => coeff H μH n *
      (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) :=
  measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet).comp
    (measurable_subtype_coe.mul_const g))

private theorem lintegral_weight_mul_ne_top [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH ≠ ⊤ := by
  simp_rw [weight_eq H μH]
  rw [lintegral_tsum fun n => (measurable_term H μH n g).aemeasurable]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => lintegral_term_le H μH n g)
  rw [ENNReal.tsum_geometric]
  simp

private theorem lintegral_weight_mul_ne_zero [μH.IsHaarMeasure] (hH : IsClosed (H : Set G)) (g : G) :
    ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH ≠ 0 := by
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem g
  have hg : g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) :=
    (CompactExhaustion.choice G).subset_interior_succ n hn
  set U : Set H := {x : H | (x : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G)} with hU
  have hUopen : IsOpen U := isOpen_interior.preimage (continuous_subtype_val.mul continuous_const)
  have hU1 : (1 : H) ∈ U := by
    show ((1 : H) : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G)
    simpa using hg

  have hcompact : IsCompact (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)) :=
    (hH.isClosedEmbedding_subtypeVal).isCompact_preimage
      (((CompactExhaustion.choice G).isCompact (n + 1)).mul ((CompactExhaustion.choice G).isCompact (n + 1)).inv)
  have hcoeff : coeff H μH n ≠ 0 := by
    unfold coeff
    refine mul_ne_zero (pow_ne_zero _ (by simp)) (ENNReal.inv_ne_zero.mpr ?_)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hcompact.measure_lt_top.ne⟩

  have hterm : coeff H μH n * μH U ≤ ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH := by
    rw [← lintegral_indicator_const hUopen.measurableSet]
    refine lintegral_mono fun x => ?_
    rw [weight_eq H μH]
    refine le_trans ?_ (ENNReal.le_tsum n)
    by_cases hx : x ∈ U
    · have hxg : (x : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) := hx
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hxg]
    · simp [Set.indicator_of_notMem hx]
  refine ne_of_gt (lt_of_lt_of_le ?_ hterm)
  exact ENNReal.mul_pos hcoeff (hUopen.measure_pos μH ⟨1, hU1⟩).ne'

end DensNorm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

section Density
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

variable [OpensMeasurableSpace G]

private theorem measurable_weight (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · refine Measurable.tsum fun n => ?_
    exact (measurable_const.indicator isOpen_interior.measurableSet).const_mul _
  · exact measurable_const

private theorem measurable_lintegral_weight_mul [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (H : Subgroup G)
    (μH : Measure H) [SFinite μH] : Measurable fun g : G => ∫⁻ x : H, HaarQuotient.weight H μH ((x : G) * g) ∂μH := by
  have hm : Measurable fun p : H × G => HaarQuotient.weight H μH ((p.1 : G) * p.2) :=
    (measurable_weight H μH).comp ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
  exact hm.lintegral_prod_left

private theorem measurable_density [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] (H : Subgroup G)
    (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  unfold HaarQuotient.density
  exact (measurable_weight H μH).div (measurable_lintegral_weight_mul H μH)

end Density
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

end ArchFiniteFactorisation
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

namespace ArchFiniteFactorisation

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

private scoped instance : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)

private scoped instance : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩

private theorem isClosed_adelicUnipotent :
    IsClosed ((adelicUnipotent ℚ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :=
  isClosed_range_unipotentGL2Hom

private theorem isClosed_realUnipotent :
    IsClosed ((realUnipotent : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) :=
  isClosed_range_unipotentGL2Hom

private theorem isClosed_finUnipotent :
    IsClosed ((finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) :=
  isClosed_subgroupOf _ _ isClosed_range_unipotentGL2Hom

private theorem isHaarMeasure_unipotentHaar :
    (unipotentHaar ℚ).IsHaarMeasure ∧ (unipotentHaar ℚ).IsMulRightInvariant :=
  AutomorphicForm.isHaarMeasure_and_isMulRightInvariant_unipotentHaar ℚ

private theorem isHaarMeasure_archMeasure : archMeasure.IsHaarMeasure ∧ archMeasure.IsMulRightInvariant :=
  LanglandsTunnell.Converse.isHaarMeasure_and_isMulRightInvariant_archMeasure

private theorem main
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)] :
    ∀
    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNArch : Measure realUnipotent) [μNArch.IsHaarMeasure]
    (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure]
    (_hsplit : Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (LanglandsTunnell.ratArchGL2 g, RSCarrier.finFactor g))
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
        RSCarrier.archMeasure.prod μf)
    (_hNsplit : Measure.map
        (fun n : adelicUnipotent ℚ => (LanglandsTunnell.ratArchGL2 n, RSCarrier.finFactor n))
        (unipotentHaar ℚ) =
        (Measure.map Subtype.val μNArch).prod (Measure.map Subtype.val μNFin))
    (s : ℂ)
    (WArch FArch : GL (Fin 2) ℝ → ℂ) (Wf Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hf : ∀ g, f g =
      ((WArch (ratArchGL2 g) * FArch (ratArchGL2 g)) *
          (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
        ((Wf (finFactor g) * Ff (finFactor g)) *
          ((TateGlobal.ideleNorm ℚ
              (Matrix.GeneralLinearGroup.det (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2))))
    (_hfm : Measurable f)
    (_hinv : ∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f g)
    (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ) (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q)
    (_hint : Integrable (fun p : GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ =>
        ((WArch p.1 * FArch p.1) * (((|(Matrix.GeneralLinearGroup.det p.1 : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
          ((Wf p.2 * Ff p.2) *
            ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ)
              ^ (s - 1 / 2))))
      ((archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)).prod
        (μf.withDensity (HaarQuotient.density finUnipotent μNFin)))),
    ∫ q, f (σq q) ∂(unipotentQuotientMeasure ℚ) =
      rsArchIntegral archMeasure μNArch s WArch FArch * rsFinIntegral μf μNFin s Wf Ff := by
  intro μf _ μNArch _ μNFin _ hsplit hNsplit s WArch FArch Wf Ff f hf hfm hinv σq hσq hint

  haveI hNH : (unipotentHaar ℚ).IsHaarMeasure := isHaarMeasure_unipotentHaar.1
  haveI hNR : (unipotentHaar ℚ).IsMulRightInvariant := isHaarMeasure_unipotentHaar.2
  haveI hAH : archMeasure.IsHaarMeasure := isHaarMeasure_archMeasure.1

  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  haveI : SigmaFinite (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := sigmaFinite_adelicGLHaar
  haveI : SecondCountableTopology (finiteAdelicGL2Subgroup ℚ) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 2) ℝ) := secondCountableTopology_generalLinearGroup
  haveI : SigmaCompactSpace realUnipotent := sigmaCompactSpace_of_isClosed _ isClosed_realUnipotent
  haveI : SigmaCompactSpace finUnipotent := sigmaCompactSpace_of_isClosed _ isClosed_finUnipotent

  haveI : LocallyCompactSpace (GL (Fin 2) ℝ) := locallyCompactSpace_gl_real
  haveI : LocallyCompactSpace (AdelicGL2 (𝓞 ℚ) ℚ) := locallyCompactSpace_generalLinearGroup
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) :=
    locallyCompactSpace_of_isClosed _ (isClosed_finiteAdelicGL2Subgroup ℚ)
  haveI : μNArch.IsMulRightInvariant := isMulRightInvariant_of_comm μNArch (range_mul_comm _)
  haveI : μNFin.IsMulRightInvariant :=
    isMulRightInvariant_of_comm μNFin (subgroupOf_mul_comm _ _ (range_mul_comm _))
  have hαArch : ∀ g : GL (Fin 2) ℝ,
      ∫⁻ h : realUnipotent, HaarQuotient.density realUnipotent μNArch ((h : GL (Fin 2) ℝ) * g) ∂μNArch = 1 :=
    HaarQuotient.lintegral_density_mul_eq_one realUnipotent isClosed_realUnipotent μNArch
  have hαf : ∀ g : finiteAdelicGL2Subgroup ℚ,
      ∫⁻ h : finUnipotent, HaarQuotient.density finUnipotent μNFin ((h : finiteAdelicGL2Subgroup ℚ) * g) ∂μNFin =
        1 :=
    HaarQuotient.lintegral_density_mul_eq_one finUnipotent isClosed_finUnipotent μNFin

  have hρ₁ : Measurable (HaarQuotient.density realUnipotent μNArch) := measurable_density _ _
  have hρ₂ : Measurable (HaarQuotient.density finUnipotent μNFin) := measurable_density _ _
  have hΘ : Measurable fun g : AdelicGL2 (𝓞 ℚ) ℚ => (ratArchGL2 g, finFactor g) :=
    continuous_ratArchGL2.measurable.prodMk continuous_finFactor.measurable

  set ρ : AdelicGL2 (𝓞 ℚ) ℚ → ℝ≥0∞ := fun g =>
    HaarQuotient.density realUnipotent μNArch (ratArchGL2 g) *
      HaarQuotient.density finUnipotent μNFin (finFactor g) with hρ_def
  have hρ : Measurable ρ :=
    (hρ₁.comp continuous_ratArchGL2.measurable).mul (hρ₂.comp continuous_finFactor.measurable)

  have hρ1 : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ∫⁻ n : adelicUnipotent ℚ, ρ ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) ∂(unipotentHaar ℚ) = 1 := by
    intro g
    have hfun : (fun n : adelicUnipotent ℚ => ρ ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g)) =
        fun n : adelicUnipotent ℚ =>
          (fun a : GL (Fin 2) ℝ => HaarQuotient.density realUnipotent μNArch (a * ratArchGL2 g))
              (ratArchGL2 (n : AdelicGL2 (𝓞 ℚ) ℚ), finFactor (n : AdelicGL2 (𝓞 ℚ) ℚ)).1 *
            (fun b : finiteAdelicGL2Subgroup ℚ => HaarQuotient.density finUnipotent μNFin (b * finFactor g))
              (ratArchGL2 (n : AdelicGL2 (𝓞 ℚ) ℚ), finFactor (n : AdelicGL2 (𝓞 ℚ) ℚ)).2 := by
      funext n
      simp only [hρ_def, ratArchGL2_mul, finFactor_mul]
    rw [hfun]
    exact lintegral_mul_comp_eq_one (unipotentHaar ℚ) (μNArch.map Subtype.val) (μNFin.map Subtype.val)
      (hΘ.comp measurable_subtype_coe) hNsplit (hρ₁.comp (measurable_mul_const _))
      (hρ₂.comp (measurable_mul_const _))
      (lintegral_map_val_mul_eq_one realUnipotent μNArch hρ₁ _ (hαArch _))
      (lintegral_map_val_mul_eq_one finUnipotent μNFin hρ₂ _ (hαf _))

  have hν : ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).withDensity ρ).map
      (Quotient.mk'' : AdelicGL2 (𝓞 ℚ) ℚ → UnipotentQuotient ℚ) = unipotentQuotientMeasure ℚ :=
    map_withDensity_eq_of_unfolding (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) (unipotentHaar ℚ)
      (unipotentQuotientMeasure ℚ)
      (fun F hF => HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) (adelicUnipotent ℚ) isClosed_adelicUnipotent (unipotentHaar ℚ)
        F hF)
      ρ hρ hρ1

  rw [← hν, integral_comp_section_map_mk _ hfm (section_eq_of_invariant hinv hσq)]
  simp_rw [hf]
  exact integral_withDensity_mul_comp_eq_mul (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) hΘ archMeasure μf hsplit
    hρ₁ hρ₂
    (fun a : GL (Fin 2) ℝ =>
      (WArch a * FArch a) * (((|(Matrix.GeneralLinearGroup.det a : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
    (fun b : finiteAdelicGL2Subgroup ℚ =>
      (Wf b * Ff b) *
        ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (b : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
    hint

end ArchFiniteFactorisation
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

namespace ArchFiniteFactorisation

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

private scoped instance instMeasGLR : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)
private scoped instance instBorelGLR : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩

theorem integrable_norm_out_of_integrable_prod
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNArch : Measure realUnipotent) [μNArch.IsHaarMeasure]
    (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure]
    (hsplit : Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (LanglandsTunnell.ratArchGL2 g, RSCarrier.finFactor g))
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
        RSCarrier.archMeasure.prod μf)
    (hNsplit : Measure.map
        (fun n : adelicUnipotent ℚ => (LanglandsTunnell.ratArchGL2 n, RSCarrier.finFactor n))
        (unipotentHaar ℚ) =
        (Measure.map Subtype.val μNArch).prod (Measure.map Subtype.val μNFin))
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (P : GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ → ℂ)
    (hfP : ∀ g, f g = P (ratArchGL2 g, finFactor g))
    (hfm : Measurable f)
    (hinv : ∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f g)
    (hint : Integrable P
      ((archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)).prod
        (μf.withDensity (HaarQuotient.density finUnipotent μNFin)))) :
    Integrable (fun q : UnipotentQuotient ℚ => ‖f q.out‖) (unipotentQuotientMeasure ℚ) := by
  haveI hNH : (unipotentHaar ℚ).IsHaarMeasure := isHaarMeasure_unipotentHaar.1
  haveI hNR : (unipotentHaar ℚ).IsMulRightInvariant := isHaarMeasure_unipotentHaar.2
  haveI hAH : archMeasure.IsHaarMeasure := isHaarMeasure_archMeasure.1
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  haveI : SigmaFinite (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := sigmaFinite_adelicGLHaar
  haveI : SecondCountableTopology (finiteAdelicGL2Subgroup ℚ) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 2) ℝ) := secondCountableTopology_generalLinearGroup
  haveI : SigmaCompactSpace realUnipotent := sigmaCompactSpace_of_isClosed _ isClosed_realUnipotent
  haveI : SigmaCompactSpace finUnipotent := sigmaCompactSpace_of_isClosed _ isClosed_finUnipotent
  haveI : LocallyCompactSpace (GL (Fin 2) ℝ) := locallyCompactSpace_gl_real
  haveI : LocallyCompactSpace (AdelicGL2 (𝓞 ℚ) ℚ) := locallyCompactSpace_generalLinearGroup
  haveI : LocallyCompactSpace (finiteAdelicGL2Subgroup ℚ) :=
    locallyCompactSpace_of_isClosed _ (isClosed_finiteAdelicGL2Subgroup ℚ)
  haveI : μNArch.IsMulRightInvariant := isMulRightInvariant_of_comm μNArch (range_mul_comm _)
  haveI : μNFin.IsMulRightInvariant :=
    isMulRightInvariant_of_comm μNFin (subgroupOf_mul_comm _ _ (range_mul_comm _))
  have hαArch : ∀ g : GL (Fin 2) ℝ,
      ∫⁻ h : realUnipotent, HaarQuotient.density realUnipotent μNArch ((h : GL (Fin 2) ℝ) * g) ∂μNArch = 1 :=
    HaarQuotient.lintegral_density_mul_eq_one realUnipotent isClosed_realUnipotent μNArch
  have hαf : ∀ g : finiteAdelicGL2Subgroup ℚ,
      ∫⁻ h : finUnipotent, HaarQuotient.density finUnipotent μNFin ((h : finiteAdelicGL2Subgroup ℚ) * g) ∂μNFin =
        1 :=
    HaarQuotient.lintegral_density_mul_eq_one finUnipotent isClosed_finUnipotent μNFin
  have hρ₁ : Measurable (HaarQuotient.density realUnipotent μNArch) := measurable_density _ _
  have hρ₂ : Measurable (HaarQuotient.density finUnipotent μNFin) := measurable_density _ _
  have hΘ : Measurable fun g : AdelicGL2 (𝓞 ℚ) ℚ => (ratArchGL2 g, finFactor g) :=
    continuous_ratArchGL2.measurable.prodMk continuous_finFactor.measurable
  set ρ : AdelicGL2 (𝓞 ℚ) ℚ → ℝ≥0∞ := fun g =>
    HaarQuotient.density realUnipotent μNArch (ratArchGL2 g) *
      HaarQuotient.density finUnipotent μNFin (finFactor g) with hρ_def
  have hρ : Measurable ρ :=
    (hρ₁.comp continuous_ratArchGL2.measurable).mul (hρ₂.comp continuous_finFactor.measurable)
  have hρ1 : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ∫⁻ n : adelicUnipotent ℚ, ρ ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) ∂(unipotentHaar ℚ) = 1 := by
    intro g
    have hfun : (fun n : adelicUnipotent ℚ => ρ ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g)) =
        fun n : adelicUnipotent ℚ =>
          (fun a : GL (Fin 2) ℝ => HaarQuotient.density realUnipotent μNArch (a * ratArchGL2 g))
              (ratArchGL2 (n : AdelicGL2 (𝓞 ℚ) ℚ), finFactor (n : AdelicGL2 (𝓞 ℚ) ℚ)).1 *
            (fun b : finiteAdelicGL2Subgroup ℚ => HaarQuotient.density finUnipotent μNFin (b * finFactor g))
              (ratArchGL2 (n : AdelicGL2 (𝓞 ℚ) ℚ), finFactor (n : AdelicGL2 (𝓞 ℚ) ℚ)).2 := by
      funext n
      simp only [hρ_def, ratArchGL2_mul, finFactor_mul]
    rw [hfun]
    exact lintegral_mul_comp_eq_one (unipotentHaar ℚ) (μNArch.map Subtype.val) (μNFin.map Subtype.val)
      (hΘ.comp measurable_subtype_coe) hNsplit (hρ₁.comp (measurable_mul_const _))
      (hρ₂.comp (measurable_mul_const _))
      (lintegral_map_val_mul_eq_one realUnipotent μNArch hρ₁ _ (hαArch _))
      (lintegral_map_val_mul_eq_one finUnipotent μNFin hρ₂ _ (hαf _))
  have hν : ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).withDensity ρ).map
      (Quotient.mk'' : AdelicGL2 (𝓞 ℚ) ℚ → UnipotentQuotient ℚ) = unipotentQuotientMeasure ℚ :=
    map_withDensity_eq_of_unfolding (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) (unipotentHaar ℚ)
      (unipotentQuotientMeasure ℚ)
      (fun F hF => HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) (adelicUnipotent ℚ) isClosed_adelicUnipotent (unipotentHaar ℚ)
        F hF)
      ρ hρ hρ1
  have hsec : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖f (Quotient.mk'' g : UnipotentQuotient ℚ).out‖ = ‖f g‖ := fun g => by
    rw [section_eq_of_invariant hinv (fun q : UnipotentQuotient ℚ => Quotient.out_eq' q) g]
  have hcomp : ((fun q : UnipotentQuotient ℚ => ‖f q.out‖) ∘ (Quotient.mk'' : AdelicGL2 (𝓞 ℚ) ℚ → UnipotentQuotient ℚ)) =
      fun g => ‖f g‖ := funext hsec
  have hmeasQ : Measurable (fun q : UnipotentQuotient ℚ => ‖f q.out‖) := by
    refine measurable_from_quotient.2 ?_
    rw [hcomp]
    exact hfm.norm
  rw [← hν]
  refine (integrable_map_measure hmeasQ.aestronglyMeasurable measurable_quotient_mk''.aemeasurable).mpr ?_
  rw [hcomp]
  have hmap : ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).withDensity ρ).map
        (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (ratArchGL2 g, finFactor g)) =
      (archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)).prod
        (μf.withDensity (HaarQuotient.density finUnipotent μNFin)) := by
    have hρ' : Measurable fun p : GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ =>
        HaarQuotient.density realUnipotent μNArch p.1 * HaarQuotient.density finUnipotent μNFin p.2 :=
      (hρ₁.comp measurable_fst).mul (hρ₂.comp measurable_snd)
    have h := map_withDensity_comp' (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) hΘ hρ'
    rw [hsplit, ← prod_withDensity₀ hρ₁.aemeasurable hρ₂.aemeasurable] at h
    exact h
  have hfΘ : f = P ∘ fun g : AdelicGL2 (𝓞 ℚ) ℚ => (ratArchGL2 g, finFactor g) := funext hfP
  have hPint : Integrable P (((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).withDensity ρ).map
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (ratArchGL2 g, finFactor g))) := by rw [hmap]; exact hint
  have hfint : Integrable f ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).withDensity ρ) := by
    rw [hfΘ]
    exact (integrable_map_measure hPint.aestronglyMeasurable hΘ.aemeasurable).mp hPint
  exact hfint.norm

end ArchFiniteFactorisation
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

noncomputable section

namespace Ws46
namespace RS22Split

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.TateGlobal NumberField.InfinitePlace.Completion

theorem coe_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

theorem glArch_archRealGLAt_ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glArch (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g)) =
      glArch (𝓞 ℚ) ℚ g := by
  have h := (RSCarrier.finFactor g).2
  rw [mem_finiteAdelicGL2Subgroup_iff, coe_finFactor, map_mul, map_inv, inv_mul_eq_one] at h
  exact h

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem abs_det_ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    |(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| = archDetNorm (default : InfinitePlace ℚ) g := by
  unfold archDetNorm LanglandsTunnell.ratArchGL2
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have hcoe : ((Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
        (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace
          ℚ))).toRingHom.mapMatrix
        ((archComponent ℚ default (glArch (𝓞 ℚ) ℚ g) : GL (Fin 2) (default : InfinitePlace ℚ).Completion) :
          Matrix (Fin 2) (Fin 2) (default : InfinitePlace ℚ).Completion) := rfl
  rw [hcoe, ← RingHom.map_det, ← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero (map_zero _) _

theorem ideleNorm_det_eq_archAbs_mul_finNorm (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) =
      |(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| *
        TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
  have hg : archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g) *
      (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
    rw [coe_finFactor, mul_inv_cancel_left]
  conv_lhs => rw [← hg]
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
  congr 1
  have hX : glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g)) ∈
      finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    rw [glFin_archRealGLAt]; exact one_mem _
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult ℚ _ hX, Fintype.prod_subsingleton _ default]
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    simp [NumberField.InfinitePlace.mult, IsTotallyReal.isReal]
  rw [hmult, pow_one, abs_det_ratArchGL2]
  unfold archDetNorm
  rw [glArch_archRealGLAt_ratArchGL2]

theorem ideleNorm_det_cpow_split (g : AdelicGL2 (𝓞 ℚ) ℚ) (z : ℂ) :
    ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ z =
      (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ z) *
        ((TateGlobal.ideleNorm ℚ
          (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ z) := by
  rw [ideleNorm_det_eq_archAbs_mul_finNorm, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (NumberField.TateGlobal.ideleNorm_pos _).le]

theorem det_unipotent_mul (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    Matrix.GeneralLinearGroup.det ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = Matrix.GeneralLinearGroup.det g := by
  obtain ⟨x, hx⟩ := n.2
  rw [map_mul, ← hx]
  have : Matrix.GeneralLinearGroup.det (unipotentGL2Hom x : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    apply Units.ext
    change ((unipotentGL2 (Multiplicative.toAdd x) : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det = 1
    rw [unipotentGL2_coe, Matrix.det_fin_two_of]
    ring
  rw [this, one_mul]

theorem bottomRowVec_unipotent_mul (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) (t : AdeleRing (𝓞 ℚ) ℚ) :
    bottomRowVec ℚ ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) t = bottomRowVec ℚ g t := by
  obtain ⟨x, hx⟩ := n.2
  funext j
  unfold bottomRowVec
  rw [← hx]
  change t * (((unipotentGL2 (Multiplicative.toAdd x)) * g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j = _
  rw [Units.val_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem rs22Kernel_unipotent_mul (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (s : ℂ)
    (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) =
      rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s g := by
  rw [rs22Kernel_def, rs22Kernel_def, det_unipotent_mul, bottomRowVec_unipotent_mul]

end Ws46.RS22Split
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat.ArchFiniteFactorisation"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

open ArchFiniteFactorisation Ws46.RS22Split in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (WA WA' FA : GL (Fin 2) ℝ → ℂ) (Wf Wf' Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
    (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (P : ℝ → ℝ) (x₀ : ℝ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (e₁ e₂ cS uS : ℝ) (tS : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hφc : Continuous φ) (_hφ'c : Continuous φ')
    (_hφd : IsRapidlyDecreasingOnSiegelSets ℚ φ) (_hφ'd : IsRapidlyDecreasingOnSiegelSets ℚ φ')
    (_hφG : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (_hφ'G : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (globalPoints (𝓞 ℚ) ℚ γ * g) = φ' g)
    (_hΦ : Φ ∈ schwartzBruhat2 ℚ)
    (_he₁ : 0 < e₁) (_he : e₁ < e₂) (_hcS : 0 < cS) (_hDm : MeasurableSet D)
    (_hDμ : adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ D < ⊤)
    (_hDs : D ⊆ {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (_hDS : D ⊆ ⋃ t ∈ tS, (· * t) '' integralWindowedSiegelSet ℚ cS uS)
    (_hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g))
    (_hW' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g = WA' (ratArchGL2 g) * Wf' (finFactor g))
    (_hΦsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Φ (bottomRowVec ℚ g 1) = FA (ratArchGL2 g) * Ff (finFactor g))
    (_hFA : ∀ g : GL (Fin 2) ℝ, FA g = Complex.exp (-(Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))
    (_hT : ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
      WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') * WA' (upperUnit a₁ 0 a₂ h₁ h₂.ne') = ((P (a₁ / a₂) : ℝ) : ℂ))
    (_hP0 : ∀ y : ℝ, 0 ≤ P y)
    (_hPint : ∀ σ' : ℝ, x₀ < σ' → Integrable (fun y : ℝ => P y * |y| ^ (σ' - 2)))
    (_hWfm : Measurable Wf) (_hWf'm : Measurable Wf') (_hFfm : Measurable Ff)
    (_harch : @Measurable (GL (Fin 2) ℝ) ℂ (borel _) _ WA ∧ @Measurable (GL (Fin 2) ℝ) ℂ (borel _) _ WA' ∧ Measurable P ∧
      (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, WA (n * g) * WA' (n * g) = WA g * WA' g) ∧
      (∀ κ' ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ' = 1 →
        ∀ g : GL (Fin 2) ℝ, WA (g * κ') * WA' (g * κ') = WA g * WA' g))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (_hfin :
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        Wf ((n : finiteAdelicGL2Subgroup ℚ) * g) * (Wf' ((n : finiteAdelicGL2Subgroup ℚ) * g) * Ff ((n : finiteAdelicGL2Subgroup ℚ) * g)) =
          Wf g * (Wf' g * Ff g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ →
          Wf' (finFactor (g * placeEmbed ℚ v x)) * Ff (finFactor (g * placeEmbed ℚ v x)) = Wf' (finFactor g) * Ff (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ hv : v ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
        Wf (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
          (Wf' (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
            Ff (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)))) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om v * om' v) ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) m.toNat
         else 0) * (Wf (finFactor g) * (Wf' (finFactor g) * Ff (finFactor g)))))
    (_hsupp :
      (∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
        (∀ g : finiteAdelicGL2Subgroup ℚ, ‖Wf g * (Wf' g * Ff g)‖ ≤ B₀) ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf g * (Wf' g * Ff g) ≠ 0 →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)))
    :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∃ σd : ℝ, ∀ s : ℂ, σd < s.re →
      ∀ (ν₀ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [ν₀.IsHaarMeasure]
        (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
        (μNArch : Measure realUnipotent) [μNArch.IsHaarMeasure]
        (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
      Integrable (fun q : UnipotentQuotient ℚ =>
          ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 q.out *
            whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 q.out *
            rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) q.out‖)
        (unipotentQuotientMeasure ℚ) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo ℚ

  obtain ⟨μf₀, hμf₀, -, hsplit⟩ := LanglandsTunnell.Converse.exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure
  obtain ⟨μNA₀, μNF₀, hNA₀, hNF₀, hNsplit⟩ :=
    LanglandsTunnell.Converse.exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
  haveI := hμf₀; haveI := hNA₀; haveI := hNF₀

  obtain ⟨σC, hC⟩ := LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_gaussian_rpow_det_rat c u d₁ d₂ T S φ φ' WA WA' FA Wf Wf' Ff Φ P x₀ D e₁ e₂ cS uS tS _hφc _hφ'c _hφd _hφ'd _hφG _hφ'G _hΦ _he₁ _he _hcS _hDm _hDμ _hDs _hDS _hW _hW' _hΦsplit _hFA _hT _hP0 _hPint _hWfm _hWf'm _hFfm _harch ϖ hπ lam om lam' om' κ _hfin _hsupp
  obtain ⟨σD, hD⟩ := LanglandsTunnell.RankinSelberg.exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat c u d₁ d₂ T S φ φ' WA WA' FA Wf Wf' Ff Φ P x₀ D e₁ e₂ cS uS tS _hφc _hφ'c _hφd _hφ'd _hφG _hφ'G _hΦ _he₁ _he _hcS _hDm _hDμ _hDs _hDS _hW _hW' _hΦsplit _hFA _hT _hP0 _hPint _hWfm _hWf'm _hFfm _harch ϖ hπ lam om lam' om' κ _hfin _hsupp
  have hwinv := LanglandsTunnell.RankinSelberg.whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat c u d₁ d₂ T S φ φ' WA WA' FA Wf Wf' Ff Φ P x₀ D e₁ e₂ cS uS tS _hφc _hφ'c _hφd _hφ'd _hφG _hφ'G _hΦ _he₁ _he _hcS _hDm _hDμ _hDs _hDS _hW _hW' _hΦsplit _hFA _hT _hP0 _hPint _hWfm _hWf'm _hFfm _harch ϖ hπ lam om lam' om' κ _hfin _hsupp
  obtain ⟨hWAm, hWA'm, hPm, hN, hK⟩ := _harch
  refine ⟨max σC σD, fun s hs ν₀ _ μf _ μNArch _ μNFin _ => ?_⟩
  have hC' := hC s (lt_of_le_of_lt (le_max_left _ _) hs) ν₀ μf₀ μNA₀ μNF₀
  have hD' := hD s (lt_of_le_of_lt (le_max_right _ _) hs) ν₀ μf₀ μNA₀ μNF₀
  have hint := MeasureTheory.Integrable.mul_prod hC' hD'

  have hfP : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g *
          whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g *
          rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) g =
      (fun p : GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ =>
        ((WA p.1 * (WA' p.1 * Complex.exp (-(Real.pi *
            (((p.1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((p.1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
            (((|(Matrix.GeneralLinearGroup.det p.1 : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2))) *
          ((Wf (finFactor (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)) * (Wf' (finFactor (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)) * Ff (finFactor (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)))) *
            ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)))
        (ratArchGL2 g, finFactor g) := by
    intro g
    simp only []
    rw [rs22Kernel_def, _hW g, _hW' g, _hΦsplit g, _hFA, cpowChar_apply_val, val_moduleChar_apply,
      show s - 1 / 2 + 1 / 2 = s + 1 / 2 - 1 / 2 by ring, ideleNorm_det_cpow_split g, MonoidHom.one_apply, Units.val_one,
      finFactor_coe]
    ring

  have hGc : Continuous fun p₁ : GL (Fin 2) ℝ => Complex.exp (-(Real.pi *
      (((p₁ : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((p₁ : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)) := by
    have h1 : Continuous fun g : GL (Fin 2) ℝ => (Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2)) :=
      (continuous_const.mul (((Units.continuous_val.matrix_elem 1 0).pow 2).add
        ((Units.continuous_val.matrix_elem 1 1).pow 2)))
    exact ((Complex.continuous_ofReal.comp h1).neg).cexp
  have hdetc : Continuous fun g : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det g : ℝ) := by
    have h1 : (fun g : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det g : ℝ)) =
        fun g : GL (Fin 2) ℝ => ((g : Matrix (Fin 2) (Fin 2) ℝ)).det :=
      funext fun g => Matrix.GeneralLinearGroup.val_det_apply g
    rw [h1]; exact Units.continuous_val.matrix_det
  have hAm : Measurable fun p₁ : GL (Fin 2) ℝ => (WA p₁ * (WA' p₁ * Complex.exp (-(Real.pi *
      (((p₁ : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((p₁ : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))) *
      (((|(Matrix.GeneralLinearGroup.det p₁ : ℝ)| : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) :=
    (hWAm.mul (hWA'm.mul hGc.measurable)).mul
      ((Complex.continuous_ofReal.comp (continuous_abs.comp hdetc)).measurable.pow_const _)
  have hNc : Continuous fun b : finiteAdelicGL2Subgroup ℚ =>
      ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (b : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm_det ℚ).comp continuous_subtype_val)
  have hffm : Measurable fun b : finiteAdelicGL2Subgroup ℚ => finFactor (b : AdelicGL2 (𝓞 ℚ) ℚ) :=
    (continuous_finFactor.comp continuous_subtype_val).measurable
  have hBm : Measurable fun b : finiteAdelicGL2Subgroup ℚ =>
      (Wf (finFactor (b : AdelicGL2 (𝓞 ℚ) ℚ)) * (Wf' (finFactor (b : AdelicGL2 (𝓞 ℚ) ℚ)) * Ff (finFactor (b : AdelicGL2 (𝓞 ℚ) ℚ)))) *
      ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (b : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2) :=
    ((_hWfm.comp hffm).mul ((_hWf'm.comp hffm).mul (_hFfm.comp hffm))).mul (hNc.measurable.pow_const _)
  have hPm := (hAm.comp measurable_fst).mul (hBm.comp measurable_snd)
  have hΘ : Measurable fun g : AdelicGL2 (𝓞 ℚ) ℚ => (ratArchGL2 g, finFactor g) :=
    continuous_ratArchGL2.measurable.prodMk continuous_finFactor.measurable
  have hfm : Measurable fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g *
          whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g *
          rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) g := by
    rw [funext hfP]
    exact hPm.comp hΘ

  have hinv : ∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g *
          whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g *
          rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) g) ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) =
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g *
          whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g *
          rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) g) g := by
    intro n g
    simp only []
    rw [hwinv n g, rs22Kernel_unipotent_mul]
  exact integrable_norm_out_of_integrable_prod μf₀ μNA₀ μNF₀ hsplit hNsplit _ _ hfP hfm hinv hint

end
end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_norm_whittakerCoefficient_mul_rs22Kernel_unipotentQuotient_rat (solution)
