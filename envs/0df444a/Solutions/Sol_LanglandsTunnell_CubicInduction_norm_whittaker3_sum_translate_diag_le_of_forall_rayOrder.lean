-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.norm_whittaker3_sum_translate_diag_le_of_forall_rayOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e5535a9f-00f8-553c-adf9-f8219217091c

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv
import Theorems.Thm_LanglandsTunnell_CubicInduction_conditions_foldr_archDeriv
import Theorems.Thm_LanglandsTunnell_CubicInduction_foldr_archDeriv_mul_right_eq_sum
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum
import Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_sum_translate_diag_le_of_forall_rayOrder
p2m_attr_erase "instance" "WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply IsLocalization.map_moduleTensorEquiv_symm_tmul"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

private theorem norm_whittaker3_centralScalarGL_mul (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hφ : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * φ g)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)‖ =
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ g‖ := by
  have hz : ∀ h : AdelicGL 3 (𝓞 ℚ) ℚ,
      h * centralScalarGL 3 (𝓞 ℚ) ℚ z = centralScalarGL 3 (𝓞 ℚ) ℚ z * h := by
    intro h
    apply Units.ext
    simp only [Units.val_mul]
    show (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) =
      Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) * (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
    exact (Matrix.scalar_commute (z : AdeleRing (𝓞 ℚ) ℚ) (fun r => mul_comm _ r) _).eq.symm
  simp only [whittaker3]
  simp_rw [← mul_assoc]
  simp_rw [hz]
  simp_rw [mul_assoc, hφ, mul_assoc]
  simp_rw [MeasureTheory.integral_const_mul]
  rw [norm_mul, hω, one_mul]

private theorem ofReal_mul' (r s : ℝ) :
    AutomorphicForm.StandardKernel.ofReal (r * s) =
      AutomorphicForm.StandardKernel.ofReal r * AutomorphicForm.StandardKernel.ofReal s := by
  funext v
  exact map_mul _ r s

private theorem ofReal_zero' : AutomorphicForm.StandardKernel.ofReal 0 = 0 := by
  funext v
  exact map_zero _

private theorem ofReal_one' : AutomorphicForm.StandardKernel.ofReal 1 = 1 := by
  funext v
  exact map_one _

private theorem archRealMat3_diag (d : Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (fun i j => if i = j then d i else 0) =
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ
        (Matrix.diagonal fun i => AutomorphicForm.StandardKernel.ofReal (d i)) := by
  unfold WhittakerBlock.archRealMat3
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [h, ofReal_zero']

private theorem archMatrixInclN_diagonal_mul (x y : Fin 3 → InfiniteAdeleRing ℚ) :
    AutomorphicForm.archMatrixInclN (Fin 3) ℚ (Matrix.diagonal x) *
        AutomorphicForm.archMatrixInclN (Fin 3) ℚ (Matrix.diagonal y) =
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ (Matrix.diagonal fun i => x i * y i) := by
  rw [← AutomorphicForm.archMatrixInclN_mul, Matrix.diagonal_mul_diagonal]

private theorem isUnit_archRealMat3_diag (d : Fin 3 → ℝ) (hd : ∀ i, d i ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 (fun i j => if i = j then d i else 0)) := by
  rw [archRealMat3_diag]
  have hmul : AutomorphicForm.archMatrixInclN (Fin 3) ℚ
        (Matrix.diagonal fun i => AutomorphicForm.StandardKernel.ofReal (d i)) *
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ
        (Matrix.diagonal fun i => AutomorphicForm.StandardKernel.ofReal (d i)⁻¹) = 1 := by
    rw [archMatrixInclN_diagonal_mul]
    have hone : (fun i => AutomorphicForm.StandardKernel.ofReal (d i) *
        AutomorphicForm.StandardKernel.ofReal (d i)⁻¹) = fun _ => (1 : InfiniteAdeleRing ℚ) := by
      funext i
      rw [← ofReal_mul', mul_inv_cancel₀ (hd i), ofReal_one']
    rw [hone, Matrix.diagonal_one, AutomorphicForm.archMatrixInclN_one]
  exact ⟨⟨_, _, hmul, mul_eq_one_comm.mp hmul⟩, rfl⟩

private theorem scalar_eq_archMatrixInclN_diagonal (c : ℝ) (hc : c ≠ 0) :
    ∃ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) =
        AutomorphicForm.archMatrixInclN (Fin 3) ℚ
          (Matrix.diagonal fun _ => AutomorphicForm.StandardKernel.ofReal c) := by
  have hval : ((AutomorphicForm.StandardKernel.ofReal c, 1) : AdeleRing (𝓞 ℚ) ℚ) *
      ((AutomorphicForm.StandardKernel.ofReal c⁻¹, 1) : AdeleRing (𝓞 ℚ) ℚ) = 1 := by
    refine Prod.ext ?_ (one_mul 1)
    change AutomorphicForm.StandardKernel.ofReal c * AutomorphicForm.StandardKernel.ofReal c⁻¹ = 1
    rw [← ofReal_mul', mul_inv_cancel₀ hc, ofReal_one']
  have hval' : ((AutomorphicForm.StandardKernel.ofReal c⁻¹, 1) : AdeleRing (𝓞 ℚ) ℚ) *
      ((AutomorphicForm.StandardKernel.ofReal c, 1) : AdeleRing (𝓞 ℚ) ℚ) = 1 := by
    refine Prod.ext ?_ (one_mul 1)
    change AutomorphicForm.StandardKernel.ofReal c⁻¹ * AutomorphicForm.StandardKernel.ofReal c = 1
    rw [← ofReal_mul', inv_mul_cancel₀ hc, ofReal_one']
  refine ⟨⟨_, _, hval, hval'⟩, ?_⟩
  ext i j
  refine Prod.ext ?_ ?_
  · change NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ (Matrix.scalar (Fin 3)
        ((AutomorphicForm.StandardKernel.ofReal c, 1) : AdeleRing (𝓞 ℚ) ℚ) i j) =
      NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ (AutomorphicForm.archMatrixInclN (Fin 3) ℚ
        (Matrix.diagonal fun _ => AutomorphicForm.StandardKernel.ofReal c) i j)
    rw [AutomorphicForm.adeleArch_archMatrixInclN]
    by_cases h : i = j
    · subst h
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      rfl
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]
      exact map_zero _
  · change NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ (Matrix.scalar (Fin 3)
        ((AutomorphicForm.StandardKernel.ofReal c, 1) : AdeleRing (𝓞 ℚ) ℚ) i j) =
      NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ (AutomorphicForm.archMatrixInclN (Fin 3) ℚ
        (Matrix.diagonal fun _ => AutomorphicForm.StandardKernel.ofReal c) i j)
    rw [AutomorphicForm.adeleFin_archMatrixInclN]
    by_cases h : i = j
    · subst h
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rfl
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      exact map_zero _

private theorem exists_centralScalarGL_mul_archRealLift3_diag (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) =
        centralScalarGL 3 (𝓞 ℚ) ℚ z *
          WhittakerBlock.archRealLift3
            (fun i j => if i = j then ![a 0 / a 1 * (a 1 / a 2), a 1 / a 2, 1] i else 0) := by
  have h2 : a 2 ≠ 0 := (ha 2).ne'
  have h1 : a 1 ≠ 0 := (ha 1).ne'
  obtain ⟨z, hz⟩ := scalar_eq_archMatrixInclN_diagonal (a 2) h2
  refine ⟨z, ?_⟩
  have hu : IsUnit (WhittakerBlock.archRealMat3 (fun i j => if i = j then a i else 0)) :=
    isUnit_archRealMat3_diag a fun i => (ha i).ne'
  have hu' : IsUnit (WhittakerBlock.archRealMat3
      (fun i j => if i = j then ![a 0 / a 1 * (a 1 / a 2), a 1 / a 2, 1] i else 0)) := by
    have h0 : a 0 ≠ 0 := (ha 0).ne'
    refine isUnit_archRealMat3_diag _ fun i => ?_
    fin_cases i <;> simp [h0, h1, h2]
  rw [WhittakerBlock.archRealLift3, dif_pos hu, WhittakerBlock.archRealLift3, dif_pos hu']
  apply Units.ext
  rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
  change WhittakerBlock.archRealMat3 (fun i j => if i = j then a i else 0) =
    Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) * WhittakerBlock.archRealMat3
      (fun i j => if i = j then ![a 0 / a 1 * (a 1 / a 2), a 1 / a 2, 1] i else 0)
  rw [hz, archRealMat3_diag, archRealMat3_diag, archMatrixInclN_diagonal_mul]
  congr 2
  funext i
  rw [← ofReal_mul']
  congr 1
  fin_cases i <;> simp <;> field_simp

section WhittakerLinearity

open MeasureTheory

private theorem continuous_upperUnipotent3 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun p : A × A × A => upperUnipotent3 p.1 p.2.1 p.2.2 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun p : A × A × A =>
      (Matrix.of ![![1, p.1, p.2.2], ![0, 1, p.2.1], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun p : A × A × A =>
      (Matrix.of ![![1, -p.1, p.1 * p.2.1 - p.2.2], ![0, 1, -p.2.1], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem isProbabilityMeasure_productionPins_ν :
    @IsProbabilityMeasure _ (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
  isProbabilityMeasure_productionPinsOf_ν ℚ _ _ _ _ (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
    (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

private theorem borelSpace_productionPins_nS :
    @BorelSpace (AdeleRing (𝓞 ℚ) ℚ) _
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS := by
  rw [productionPinsOf_nS]
  exact AdelicHaar.borelSpace_adeleBorel _ _

private theorem ae_mem_adelicBox_productionPins_ν :
    ∀ᵐ a ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν,
      a ∈ AdelicBox.adelicBox ℚ := by
  rw [productionPinsOf_ν]
  unfold ProbabilityTheory.cond
  exact MeasureTheory.Measure.ae_smul_measure (ae_restrict_mem (AdelicBox.measurableSet_adelicBox ℚ)) _

private theorem continuous_integral_of_continuous {β : Type*} [TopologicalSpace β] {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α)
    (hC : IsCompact C) (hae : ∀ᵐ a ∂μ, a ∈ C) (H : β → α → ℂ) (hH : Continuous fun q : β × α => H q.1 q.2) :
    Continuous fun b => ∫ a, H b a ∂μ := by
  have hslice : ∀ b : β, Continuous fun a => H b a := fun b => hH.comp (Continuous.prodMk_right b)
  have hint : ∀ b : β, Integrable (fun a => H b a) μ := by
    intro b
    obtain ⟨Mb, hMb⟩ := hC.exists_bound_of_continuousOn (hslice b).continuousOn
    exact Integrable.of_bound (hslice b).aestronglyMeasurable Mb (hae.mono fun a ha => hMb a ha)
  refine continuous_iff_continuousAt.mpr fun b₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hH₀ : Continuous fun q : β × α => H b₀ q.2 :=
    hH.comp ((continuous_const : Continuous fun _ : β × α => b₀).prodMk continuous_snd)
  have hdist : Continuous fun q : β × α => ‖H q.1 q.2 - H b₀ q.2‖ := (hH.sub hH₀).norm
  have htube : ∀ᶠ b in nhds b₀, ∀ a ∈ C, ‖H b a - H b₀ a‖ < ε / 2 := by
    refine hC.eventually_forall_of_forall_eventually fun a _ => ?_
    refine hdist.continuousAt.eventually_lt continuous_const.continuousAt ?_
    show ‖H b₀ a - H b₀ a‖ < ε / 2
    rw [sub_self, norm_zero]
    exact half_pos hε
  refine htube.mono fun b hb => ?_
  rw [dist_eq_norm, ← integral_sub (hint b) (hint b₀)]
  have hbound : ∀ᵐ a ∂μ, ‖H b a - H b₀ a‖ ≤ ε / 2 := hae.mono fun a ha => (hb a ha).le
  calc ‖∫ a, H b a - H b₀ a ∂μ‖ ≤ ε / 2 * μ.real Set.univ := norm_integral_le_of_norm_le_const hbound
    _ = ε / 2 := by simp
    _ < ε := half_lt_self hε

private theorem integrable_of_continuous_of_ae_mem_compact {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α) (hC : IsCompact C)
    (hae : ∀ᵐ a ∂μ, a ∈ C) (K : α → ℂ) (hK : Continuous K) : Integrable K μ := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hK.continuousOn
  exact Integrable.of_bound hK.aestronglyMeasurable M (hae.mono fun a ha => hM a ha)

private theorem integral3_sum_of_continuous {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α) (hC : IsCompact C)
    (hae : ∀ᵐ a ∂μ, a ∈ C) {ι : Type*} [Fintype ι] (c : ι → ℂ) (G : ι → α → α → α → ℂ)
    (hG : ∀ i, Continuous fun p : α × α × α => G i p.1 p.2.1 p.2.2) :
    (∫ x, ∫ y, ∫ z, ∑ i, c i * G i x y z ∂μ ∂μ ∂μ) = ∑ i, c i * ∫ x, ∫ y, ∫ z, G i x y z ∂μ ∂μ ∂μ := by
  have key : ∀ K : ι → α → ℂ, (∀ i, Continuous (K i)) →
      (∫ a, ∑ i, c i * K i a ∂μ) = ∑ i, c i * ∫ a, K i a ∂μ := by
    intro K hK
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
    · intro i _
      exact (integrable_of_continuous_of_ae_mem_compact μ C hC hae (K i) (hK i)).const_mul (c i)
  have hz : ∀ i x y, Continuous fun z => G i x y z := fun i x y =>
    (hG i).comp ((Continuous.prodMk_right x).comp (Continuous.prodMk_right y))
  have hI : ∀ i, Continuous fun p : α × α => ∫ z, G i p.1 p.2 z ∂μ := fun i =>
    continuous_integral_of_continuous μ C hC hae (fun (p : α × α) z => G i p.1 p.2 z)
      ((hG i).comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)))
  have hJ : ∀ i, Continuous fun x => ∫ y, ∫ z, G i x y z ∂μ ∂μ := fun i =>
    continuous_integral_of_continuous μ C hC hae (fun x y => ∫ z, G i x y z ∂μ) (hI i)
  have h1 : ∀ x y, (∫ z, ∑ i, c i * G i x y z ∂μ) = ∑ i, c i * ∫ z, G i x y z ∂μ := fun x y =>
    key (fun i z => G i x y z) fun i => hz i x y
  have h2 : ∀ x, (∫ y, ∑ i, c i * ∫ z, G i x y z ∂μ ∂μ) = ∑ i, c i * ∫ y, ∫ z, G i x y z ∂μ ∂μ := fun x =>
    key (fun i y => ∫ z, G i x y z ∂μ) fun i => (hI i).comp (Continuous.prodMk_right x)
  simp_rw [h1, h2]
  exact key (fun i x => ∫ y, ∫ z, G i x y z ∂μ ∂μ) hJ

private theorem whittaker3_sum_mul_of_continuous {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (F : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : ∀ i, Continuous (F i)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * F i x) g =
      ∑ i, c i *
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (F i) g := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) :=
    (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
  haveI := borelSpace_productionPins_nS
  haveI := isProbabilityMeasure_productionPins_ν
  obtain ⟨C, hC, hBC⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hae : ∀ᵐ a ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν, a ∈ C :=
    ae_mem_adelicBox_productionPins_ν.mono fun a ha => hBC ha
  have hG : ∀ i, Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      F i (upperUnipotent3 p.1 p.2.1 p.2.2 * g) * NumberField.StandardAddChar.psiQ (-(p.1 + p.2.1)) := fun i =>
    ((hF i).comp ((continuous_upperUnipotent3 (A := AdeleRing (𝓞 ℚ) ℚ)).mul continuous_const)).mul
      (NumberField.StandardAddChar.continuous_psiQ.comp ((continuous_fst.add continuous_snd.fst).neg))
  unfold whittaker3
  simp_rw [Finset.sum_mul, mul_assoc]
  exact integral3_sum_of_continuous _ C hC hae c
    (fun i x y z => F i (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y))) hG

end WhittakerLinearity

private theorem whittaker3_mul_right (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (k g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (fun x => φ (x * k)) g =
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ (g * k) := by
  unfold whittaker3
  simp_rw [mul_assoc]

private theorem continuous_foldr_archDeriv_mul_right (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hφ : WhittakerBlock.IsArchSmooth3 φ)
    (hcont : ∀ w : List (Fin 3 × Fin 3),
      Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w))
    (k : AdelicGL 3 (𝓞 ℚ) ℚ) (w : List (Fin 3 × Fin 3)) :
    Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) (fun x => φ (x * k)) w) := by
  obtain ⟨coeff, -, hexp⟩ :=
    LanglandsTunnell.CubicInduction.exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum w
  have hfun : List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) (fun x => φ (x * k)) w =
      fun g => ∑ f,
        coeff k f * List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ (List.ofFn f) (g * k) :=
    funext fun g => hexp φ hφ k g
  rw [hfun]
  exact continuous_finsetSum _ fun f _ =>
    continuous_const.mul ((hcont (List.ofFn f)).comp (continuous_id.mul continuous_const))

private theorem exists_coeff_archDeriv_mul_right (i j : Fin 3) :
    ∃ a : AdelicGL 3 (𝓞 ℚ) ℚ → (Fin 1 → Fin 3 × Fin 3) → ℂ,
      (∀ f, Continuous fun k => a k f) ∧
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ k g : AdelicGL 3 (𝓞 ℚ) ℚ,
          WhittakerBlock.archDeriv i j (fun x => φ (x * k)) g =
            ∑ f, a k f * WhittakerBlock.archDeriv (f 0).1 (f 0).2 φ (g * k) := by
  obtain ⟨c, hc, he⟩ :=
    LanglandsTunnell.CubicInduction.exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum [(i, j)]
  exact ⟨c, hc, fun φ hφ k g => he φ hφ k g⟩

private theorem sum_fin_one_eq_sum_fin3 (h : Fin 3 × Fin 3 → ℝ) :
    ∑ f : Fin 1 → Fin 3 × Fin 3, h (f 0) = ∑ p : Fin 3, ∑ q : Fin 3, h (p, q) := by
  have h1 : ∑ f : Fin 1 → Fin 3 × Fin 3, h (f 0) = ∑ x : Fin 3 × Fin 3, h x :=
    Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3 × Fin 3)) _ _ fun _ => rfl
  rw [h1, Fintype.sum_prod_type]

private theorem norm_sum_mul_le (a : (Fin 1 → Fin 3 × Fin 3) → ℂ) (W : Fin 3 × Fin 3 → ℂ) (C : ℝ)
    (ha : ∀ f, ‖a f‖ ≤ C) :
    ‖∑ f : Fin 1 → Fin 3 × Fin 3, a f * W (f 0)‖ ≤ C * ∑ p : Fin 3, ∑ q : Fin 3, ‖W (p, q)‖ := by
  rw [← sum_fin_one_eq_sum_fin3 (fun x => ‖W x‖), Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha f) (norm_nonneg _)

private theorem mul_norm_le_of_mul_eq_sum {lam : ℂ} (hlam : lam ≠ 0) {y : ℝ} (hy : 0 < y) (X : ℂ)
    (W : Fin 3 → Fin 3 → ℂ) (a : (Fin 1 → Fin 3 × Fin 3) → ℂ) (C : ℝ) (ha : ∀ f, ‖a f‖ ≤ C)
    (h : lam * (y : ℂ) * X = ∑ f, a f * W (f 0).1 (f 0).2) :
    y * ‖X‖ ≤ ‖lam‖⁻¹ * C * ∑ p : Fin 3, ∑ q : Fin 3, ‖W p q‖ := by
  have hl0 : ‖lam‖ ≠ 0 := norm_ne_zero_iff.mpr hlam
  have hn : ‖lam‖ * (y * ‖X‖) = ‖∑ f, a f * W (f 0).1 (f 0).2‖ := by
    rw [← h, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy.le, mul_assoc ‖lam‖ y ‖X‖]
  have hb : ‖lam‖ * (y * ‖X‖) ≤ C * ∑ p : Fin 3, ∑ q : Fin 3, ‖W p q‖ := by
    rw [hn]
    exact norm_sum_mul_le a (fun pq => W pq.1 pq.2) C ha
  calc y * ‖X‖ = ‖lam‖⁻¹ * (‖lam‖ * (y * ‖X‖)) := by
        rw [← mul_assoc ‖lam‖⁻¹ ‖lam‖ (y * ‖X‖), inv_mul_cancel₀ hl0, one_mul]
    _ ≤ ‖lam‖⁻¹ * (C * ∑ p : Fin 3, ∑ q : Fin 3, ‖W p q‖) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg lam))
    _ = ‖lam‖⁻¹ * C * ∑ p : Fin 3, ∑ q : Fin 3, ‖W p q‖ := (mul_assoc _ _ _).symm

private theorem mul_norm_whittaker3_le_sum_norm_whittaker3_archDeriv (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hφ : WhittakerBlock.IsArchSmooth3 φ)
    (hcont : ∀ w : List (Fin 3 × Fin 3),
      Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w))
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK : IsCompact K) :
    ∃ c : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      y₁ * ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
        c * ∑ p : Fin 3, ∑ q : Fin 3,
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv p q φ)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ∧
      y₂ * ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
        c * ∑ p : Fin 3, ∑ q : Fin 3,
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv p q φ)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ := by
  have hG65 :=
    LanglandsTunnell.CubicInduction.exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv
  obtain ⟨lam, hlam, hG⟩ := hG65
  have hx01 := exists_coeff_archDeriv_mul_right 0 1
  obtain ⟨a01, ha01, he01⟩ := hx01
  have hx12 := exists_coeff_archDeriv_mul_right 1 2
  obtain ⟨a12, ha12, he12⟩ := hx12
  choose B01 hB01 using fun f => hK.exists_bound_of_continuousOn (ha01 f).continuousOn
  choose B12 hB12 using fun f => hK.exists_bound_of_continuousOn (ha12 f).continuousOn
  obtain ⟨C₀, hC01, hC12⟩ : ∃ C₀ : ℝ,
      (∀ k ∈ K, ∀ f, ‖a01 k f‖ ≤ C₀) ∧ ∀ k ∈ K, ∀ f, ‖a12 k f‖ ≤ C₀ :=
    ⟨(∑ f, |B01 f|) + ∑ f, |B12 f|,
      fun k hk f => (hB01 f k hk).trans ((le_abs_self _).trans
        ((Finset.single_le_sum (fun f' _ => abs_nonneg (B01 f')) (Finset.mem_univ f)).trans
          (le_add_of_nonneg_right (Finset.sum_nonneg fun f' _ => abs_nonneg (B12 f'))))),
      fun k hk f => (hB12 f k hk).trans ((le_abs_self _).trans
        ((Finset.single_le_sum (fun f' _ => abs_nonneg (B12 f')) (Finset.mem_univ f)).trans
          (le_add_of_nonneg_left (Finset.sum_nonneg fun f' _ => abs_nonneg (B01 f')))))⟩
  refine ⟨‖lam‖⁻¹ * C₀, fun k hk y₁ y₂ hy₁ hy₂ => ?_⟩
  have hak : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g * k) = φ (g * k) := fun γ g => by
    rw [mul_assoc]
    exact haut γ (g * k)
  obtain ⟨h01, h12⟩ := hG (fun x => φ (x * k)) (LanglandsTunnell.CubicInduction.isArchSmooth3_mul_right φ hφ k)
    (continuous_foldr_archDeriv_mul_right φ hφ hcont k) hak y₁ y₂ hy₁ hy₂
  have e01 : WhittakerBlock.archDeriv 0 1 (fun x => φ (x * k)) =
      fun g => ∑ f, a01 k f * WhittakerBlock.archDeriv (f 0).1 (f 0).2 φ (g * k) := funext (he01 φ hφ k)
  have e12 : WhittakerBlock.archDeriv 1 2 (fun x => φ (x * k)) =
      fun g => ∑ f, a12 k f * WhittakerBlock.archDeriv (f 0).1 (f 0).2 φ (g * k) := funext (he12 φ hφ k)
  have hF : ∀ f : Fin 1 → Fin 3 × Fin 3,
      Continuous fun x => WhittakerBlock.archDeriv (f 0).1 (f 0).2 φ (x * k) := fun f =>
    (hcont [f 0]).comp (continuous_id.mul continuous_const)
  rw [whittaker3_mul_right φ k, e01, whittaker3_sum_mul_of_continuous (a01 k) _ hF] at h01
  rw [whittaker3_mul_right φ k, e12, whittaker3_sum_mul_of_continuous (a12 k) _ hF] at h12
  have hW : ∀ (f : Fin 1 → Fin 3 × Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (fun x => WhittakerBlock.archDeriv (f 0).1 (f 0).2 φ (x * k)) g =
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv (f 0).1 (f 0).2 φ) (g * k) :=
    fun f g => whittaker3_mul_right _ k g
  simp only [hW] at h01 h12
  refine ⟨?_, ?_⟩
  · exact mul_norm_le_of_mul_eq_sum hlam hy₁ _
      (fun p q =>
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv p q φ)
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k))
      (a01 k) C₀ (hC01 k hk) h01
  · exact mul_norm_le_of_mul_eq_sum hlam hy₂ _
      (fun p q =>
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv p q φ)
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k))
      (a12 k) C₀ (hC12 k hk) h12

section BlockAtV

private theorem aut_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑ i, c i * f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g * t i) = ∑ i, c i * f (g * t i) := by
  simp only [mul_assoc, haut]

private theorem cen_sum_translate (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑ i, c i * f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g * t i) = (ω z : ℂ) * ∑ i, c i * f (g * t i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc (centralScalarGL 3 (𝓞 ℚ) ℚ z), hcen]
  ring

private theorem isArchSmooth3_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) {n : ℕ} (c : Fin n → ℂ)
    (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (hsm : ∀ i, WhittakerBlock.IsArchSmooth3 fun x => f (x * t i)) :
    WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) := by
  intro g
  exact ContDiffOn.sum fun i _ => contDiffOn_const.mul (hsm i g)

private theorem kfinite_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => ∑ i, c i * f (g * k * t i)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
  classical
  obtain ⟨s, hs⟩ := hKf
  refine ⟨Finset.univ.biUnion fun i => s.image fun φ g => φ (g * t i), fun k hkf hka => ?_⟩
  have hrew : (fun g => ∑ i, c i * f (g * k * t i)) =
      ∑ i, c i • LinearMap.funLeft ℂ ℂ (fun g => g * t i) (fun g => f (g * ((t i)⁻¹ * k * t i))) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show g * k * t i = g * t i * ((t i)⁻¹ * k * t i) by group]
  rw [hrew]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have hk' : (fun g => f (g * ((t i)⁻¹ * k * t i))) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) := by
    refine hs _ (fun p => ?_) ?_
    · simp [map_mul, map_inv, hkf p]
    · simpa [map_mul, map_inv, ht i] using hka
  refine Submodule.span_mono ?_
    (Submodule.apply_mem_span_image_of_mem_span (LinearMap.funLeft ℂ ℂ fun g => g * t i) hk')
  rintro _ ⟨φ, hφ, rfl⟩
  exact Finset.mem_coe.2
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem (fun φ g => φ (g * t i)) hφ⟩)

private theorem norm_whittaker3_diag_mul_eq (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hφ : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * φ g)
    (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖ =
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ
        (WhittakerBlock.archRealLift3
          (fun i j => if i = j then ![a 0 / a 1 * (a 1 / a 2), a 1 / a 2, 1] i else 0) * k)‖ := by
  obtain ⟨z, hz⟩ := exists_centralScalarGL_mul_archRealLift3_diag a ha
  rw [hz, mul_assoc, norm_whittaker3_centralScalarGL_mul ω hω φ hφ z]

end BlockAtV

section IterationAndRays

private def IsRowBlock (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (N N₂ N₃ : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
    (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) ∧
    (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) ∧
    WhittakerBlock.IsArchSmooth3 u ∧
    (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
    (∃ a : Fin (N₂ + 1) → ℂ, a (Fin.last N₂) = 1 ∧ ∑ m, a m • (WhittakerBlock.casimir2^[m] u) = 0) ∧
    (∃ a : Fin (N₃ + 1) → ℂ, a (Fin.last N₃) = 1 ∧ ∑ m, a m • (WhittakerBlock.casimir3^[m] u) = 0) ∧
    (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) ∧
    (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))

private noncomputable abbrev word (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (w : List (Fin 3 × Fin 3)) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w

private theorem isBlock_word (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (N N₂ N₃ : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hu : IsRowBlock ω N N₂ N₃ u) (w : List (Fin 3 × Fin 3)) : IsRowBlock ω N N₂ N₃ (word u w) := by
  unfold IsRowBlock at hu ⊢
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hu
  have hP :=
    LanglandsTunnell.CubicInduction.conditions_foldr_archDeriv N N₂ N₃ ω u h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ w _ rfl
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, -, -⟩ := hP
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩

private noncomputable abbrev wnorm (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₁ y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ :=
  ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ u
      (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖

private theorem bound_mul (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (Bd : ℝ → ℝ → ℝ)
    (hBd : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ → 0 ≤ Bd y₁ y₂) (Y : ℝ → ℝ → ℝ)
    (hgain : ∀ w : List (Fin 3 × Fin 3), ∃ c : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      Y y₁ y₂ * wnorm (word v w) y₁ y₂ k ≤ c * ∑ pq : Fin 3 × Fin 3, wnorm (word v (pq :: w)) y₁ y₂ k)
    (P : ℝ → ℝ → ℝ) (hP : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ → 0 ≤ P y₁ y₂)
    (hall : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      P y₁ y₂ * wnorm (word v w) y₁ y₂ k ≤ C * Bd y₁ y₂) :
    ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      P y₁ y₂ * Y y₁ y₂ * wnorm (word v w) y₁ y₂ k ≤ C * Bd y₁ y₂ := by
  intro w
  obtain ⟨c, hc⟩ := hgain w
  choose Cw hCw using fun pq : Fin 3 × Fin 3 => hall (pq :: w)
  refine ⟨|c| * ∑ pq : Fin 3 × Fin 3, |Cw pq|, fun k hk y₁ y₂ hy₁ hy₂ => ?_⟩
  have hsum0 : 0 ≤ ∑ pq : Fin 3 × Fin 3, wnorm (word v (pq :: w)) y₁ y₂ k :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc P y₁ y₂ * Y y₁ y₂ * wnorm (word v w) y₁ y₂ k
      = P y₁ y₂ * (Y y₁ y₂ * wnorm (word v w) y₁ y₂ k) := mul_assoc _ _ _
    _ ≤ P y₁ y₂ * (|c| * ∑ pq : Fin 3 × Fin 3, wnorm (word v (pq :: w)) y₁ y₂ k) :=
        mul_le_mul_of_nonneg_left ((hc k hk y₁ y₂ hy₁ hy₂).trans
          (mul_le_mul_of_nonneg_right (le_abs_self c) hsum0)) (hP y₁ y₂ hy₁ hy₂)
    _ = |c| * ∑ pq : Fin 3 × Fin 3, P y₁ y₂ * wnorm (word v (pq :: w)) y₁ y₂ k := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun pq _ => by ring
    _ ≤ |c| * ∑ pq : Fin 3 × Fin 3, |Cw pq| * Bd y₁ y₂ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun pq _ => (hCw pq k hk y₁ y₂ hy₁ hy₂).trans
          (mul_le_mul_of_nonneg_right (le_abs_self (Cw pq)) (hBd y₁ y₂ hy₁ hy₂))) (abs_nonneg c)
    _ = |c| * (∑ pq : Fin 3 × Fin 3, |Cw pq|) * Bd y₁ y₂ := by
        rw [← Finset.sum_mul, mul_assoc]

private theorem bound_pow (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (Bd : ℝ → ℝ → ℝ)
    (hBd : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ → 0 ≤ Bd y₁ y₂) (Y : ℝ → ℝ → ℝ)
    (hY : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ → 0 ≤ Y y₁ y₂)
    (hgain : ∀ w : List (Fin 3 × Fin 3), ∃ c : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      Y y₁ y₂ * wnorm (word v w) y₁ y₂ k ≤ c * ∑ pq : Fin 3 × Fin 3, wnorm (word v (pq :: w)) y₁ y₂ k)
    (P : ℝ → ℝ → ℝ) (hP : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ → 0 ≤ P y₁ y₂)
    (h0 : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      P y₁ y₂ * wnorm (word v w) y₁ y₂ k ≤ C * Bd y₁ y₂) (m : ℕ) :
    ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      P y₁ y₂ * Y y₁ y₂ ^ m * wnorm (word v w) y₁ y₂ k ≤ C * Bd y₁ y₂ := by
  induction m with
  | zero =>
    intro w
    obtain ⟨C, hC⟩ := h0 w
    exact ⟨C, fun k hk y₁ y₂ hy₁ hy₂ => by simpa only [pow_zero, mul_one] using hC k hk y₁ y₂ hy₁ hy₂⟩
  | succ m ih =>
    have hstep := bound_mul v K Bd hBd Y hgain (fun y₁ y₂ => P y₁ y₂ * Y y₁ y₂ ^ m)
      (fun y₁ y₂ hy₁ hy₂ => mul_nonneg (hP y₁ y₂ hy₁ hy₂) (pow_nonneg (hY y₁ y₂ hy₁ hy₂) m)) ih
    intro w
    obtain ⟨C, hC⟩ := hstep w
    exact ⟨C, fun k hk y₁ y₂ hy₁ hy₂ => by simpa only [pow_succ, mul_assoc] using hC k hk y₁ y₂ hy₁ hy₂⟩

private theorem regime_le_one {θ : ℝ} (hθ : 0 < θ) (M N' : ℕ) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    min y 1 ^ θ * max y 1 ^ (N' : ℝ) ≤ y ^ (0 : ℕ) * min (y ^ θ) (y ^ (-(M : ℝ))) := by
  have hM : -(M : ℝ) ≤ θ := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  rw [min_eq_left hy1, max_eq_right hy1, Real.one_rpow, mul_one, pow_zero, one_mul,
    min_eq_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 hM)]

private theorem regime_one_lt {θ : ℝ} (hθ : 0 < θ) (M N' : ℕ) {y : ℝ} (hy : 0 < y) (hy1 : 1 < y) :
    min y 1 ^ θ * max y 1 ^ (N' : ℝ) ≤ y ^ (M + N') * min (y ^ θ) (y ^ (-(M : ℝ))) := by
  have hM : -(M : ℝ) ≤ θ := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hcast : ((M + N' : ℕ) : ℝ) + -(M : ℝ) = (N' : ℝ) := by push_cast; ring
  rw [min_eq_right hy1.le, max_eq_left hy1.le, Real.one_rpow, one_mul,
    min_eq_right (Real.rpow_le_rpow_of_exponent_le hy1.le hM), ← Real.rpow_natCast, ← Real.rpow_add hy, hcast]

private theorem le_of_regimes {x₁ x₂ W C F₁ F₂ G₁ G₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hF₁ : 0 ≤ F₁)
    (hF₂ : 0 ≤ F₂) (hG₁ : 0 ≤ G₁) (h : 1 * x₁ * x₂ * W ≤ C * (F₁ * F₂)) (h₁ : F₁ ≤ x₁ * G₁) (h₂ : F₂ ≤ x₂ * G₂) :
    W ≤ |C| * (G₁ * G₂) := by
  have hx : 0 < x₁ * x₂ := mul_pos hx₁ hx₂
  have hFF : F₁ * F₂ ≤ (x₁ * x₂) * (G₁ * G₂) := by
    calc F₁ * F₂ ≤ (x₁ * G₁) * (x₂ * G₂) :=
          mul_le_mul h₁ h₂ hF₂ (mul_nonneg hx₁.le hG₁)
      _ = (x₁ * x₂) * (G₁ * G₂) := by ring
  have h' : (x₁ * x₂) * W ≤ (x₁ * x₂) * (|C| * (G₁ * G₂)) := by
    calc (x₁ * x₂) * W = 1 * x₁ * x₂ * W := by ring
      _ ≤ C * (F₁ * F₂) := h
      _ ≤ |C| * (F₁ * F₂) := mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg hF₁ hF₂)
      _ ≤ |C| * ((x₁ * x₂) * (G₁ * G₂)) := mul_le_mul_of_nonneg_left hFF (abs_nonneg C)
      _ = (x₁ * x₂) * (|C| * (G₁ * G₂)) := by ring
  exact le_of_mul_le_mul_left h' hx

private theorem rayOrder_word (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) {n : ℕ} (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hsv : WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i))) (θ₀ : ℝ)
    (hray : ∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (g * h * t i)) w} →
      (∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₁ ^ θ₀) ∧
      (∀ y₁ : ℝ, 0 < y₁ → ∃ C : ℝ, ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₂ ^ θ₀))
    (w : List (Fin 3 × Fin 3)) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u = word (fun x => ∑ i, c i * f (x * t i)) w)
    (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (fun g => u (g * k))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₁ ^ θ₀) ∧
    (∀ y₁ : ℝ, 0 < y₁ → ∃ C : ℝ, ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (fun g => u (g * k))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₂ ^ θ₀) := by
  subst hu
  have hP := LanglandsTunnell.CubicInduction.foldr_archDeriv_mul_right_eq_sum w k
  obtain ⟨m, d, ws, -, hws⟩ := hP
  refine hray _ ?_
  have hfun : (fun g => word (fun x => ∑ i, c i * f (x * t i)) w (g * k)) =
      ∑ j, d j • word (fun g => ∑ i, c i * f (g * k * t i)) (ws j) := by
    funext g
    simp only [word]
    rw [hws _ hsv g]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ws j, k, rfl⟩)

end IterationAndRays

theorem
solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hmg : IsModerateGrowth3 ℚ f)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i))
    (θ₀ : ℝ) (hθ₀ : 1 / 2 < θ₀)
    (hray : ∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (g * h * t i)) w} →
      (∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₁ ^ θ₀) ∧
      (∀ y₁ : ℝ, 0 < y₁ → ∃ C : ℝ, ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₂ ^ θ₀)) :
    ∃ θ : ℝ, 1 / 2 < θ ∧ ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ M : ℕ, ∃ C : ℝ,
      ∀ k ∈ K, ∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * f (x * t i))
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖ ≤
          C * min ((a 0 / a 1) ^ θ) ((a 0 / a 1) ^ (-(M : ℝ))) * min ((a 1 / a 2) ^ θ) ((a 1 / a 2) ^ (-(M : ℝ))) := by
  have _ := hP21
  have _ := hP12
  obtain ⟨θ, hθ₁, hθ₂⟩ : ∃ θ : ℝ, 1 / 2 < θ ∧ θ < θ₀ := ⟨(1 / 2 + θ₀) / 2, by linarith, by linarith⟩
  have hθp : 0 < θ := by linarith
  refine ⟨θ, hθ₁, fun K hK M => ?_⟩

  have hgw :=
    LanglandsTunnell.CubicInduction.continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
      f hc hmg hsa hKf n c t ht hz
  obtain ⟨hwc, N, hgrowth⟩ := hgw
  obtain ⟨-, ⟨N₂, a₂, ha₂, hrel₂⟩, ⟨N₃, a₃, ha₃, hrel₃⟩⟩ := hz
  have hsmv : WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) :=
    isArchSmooth3_sum_translate f c t fun i => LanglandsTunnell.CubicInduction.isArchSmooth3_mul_right f hsa (t i)
  have hblock : IsRowBlock ω N N₂ N₃ (fun x => ∑ i, c i * f (x * t i)) := by
    unfold IsRowBlock
    exact ⟨aut_sum_translate f haut c t, cen_sum_translate ω f hcen c t, hsmv, kfinite_sum_translate f hKf c t ht,
      ⟨a₂, ha₂, hrel₂⟩, ⟨a₃, ha₃, hrel₃⟩, hgrowth, hwc⟩

  have hW3 :=
    LanglandsTunnell.CubicInduction.norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder
      θ₀ θ hθ₂ N N₂ N₃
  obtain ⟨N', hW3⟩ := hW3
  have hF : ∀ y : ℝ, 0 < y → 0 ≤ min y 1 ^ θ * max y 1 ^ (N' : ℝ) := fun y hy =>
    mul_nonneg (Real.rpow_nonneg (le_min hy.le zero_le_one) _) (Real.rpow_nonneg (le_max_of_le_right zero_le_one) _)
  have hBd : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      0 ≤ (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ)) :=
    fun y₁ y₂ hy₁ hy₂ => mul_nonneg (hF y₁ hy₁) (hF y₂ hy₂)

  have run₁ := bound_pow (fun x => ∑ i, c i * f (x * t i)) K
    (fun y₁ y₂ : ℝ => (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ)))
    hBd (fun y₁ _ => y₁) (fun _ _ hy₁ _ => hy₁.le)
    (fun w => by
      have hb := isBlock_word ω N N₂ N₃ (fun x => ∑ i, c i * f (x * t i)) hblock w
      obtain ⟨b₁, -, b₃, -, -, -, -, b₈⟩ := hb
      have hg := mul_norm_whittaker3_le_sum_norm_whittaker3_archDeriv
        (word (fun x => ∑ i, c i * f (x * t i)) w) b₃ b₈ b₁ K hK
      obtain ⟨cg, hcg⟩ := hg
      refine ⟨cg, fun k hk y₁ y₂ hy₁ hy₂ => ?_⟩
      show y₁ * wnorm (word (fun x => ∑ i, c i * f (x * t i)) w) y₁ y₂ k ≤ cg * ∑ pq : Fin 3 × Fin 3,
        wnorm (WhittakerBlock.archDeriv pq.1 pq.2 (word (fun x => ∑ i, c i * f (x * t i)) w)) y₁ y₂ k
      rw [Fintype.sum_prod_type'
        (fun p q => wnorm (WhittakerBlock.archDeriv p q (word (fun x => ∑ i, c i * f (x * t i)) w)) y₁ y₂ k)]
      exact (hcg k hk y₁ y₂ hy₁ hy₂).1)
    (fun _ _ => (1 : ℝ)) (fun _ _ _ _ => zero_le_one)
    (fun w => by
      have hb := isBlock_word ω N N₂ N₃ (fun x => ∑ i, c i * f (x * t i)) hblock w
      obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈⟩ := hb
      have hC := hW3 ω (word (fun x => ∑ i, c i * f (x * t i)) w) (b₈ []) b₁ b₂ b₃ b₄ b₅ b₆ b₇
        (fun k _ => rayOrder_word f c t hsmv θ₀ hray w _ rfl k) K hK
      obtain ⟨C, hC⟩ := hC
      refine ⟨C, fun k hk y₁ y₂ hy₁ hy₂ => ?_⟩
      rw [one_mul, ← mul_assoc]
      exact hC k hk y₁ y₂ hy₁ hy₂)
  have run₂ := fun m₁ : ℕ => bound_pow (fun x => ∑ i, c i * f (x * t i)) K
    (fun y₁ y₂ : ℝ => (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ)))
    hBd (fun _ y₂ => y₂) (fun _ _ _ hy₂ => hy₂.le)
    (fun w => by
      have hb := isBlock_word ω N N₂ N₃ (fun x => ∑ i, c i * f (x * t i)) hblock w
      obtain ⟨b₁, -, b₃, -, -, -, -, b₈⟩ := hb
      have hg := mul_norm_whittaker3_le_sum_norm_whittaker3_archDeriv
        (word (fun x => ∑ i, c i * f (x * t i)) w) b₃ b₈ b₁ K hK
      obtain ⟨cg, hcg⟩ := hg
      refine ⟨cg, fun k hk y₁ y₂ hy₁ hy₂ => ?_⟩
      show y₂ * wnorm (word (fun x => ∑ i, c i * f (x * t i)) w) y₁ y₂ k ≤ cg * ∑ pq : Fin 3 × Fin 3,
        wnorm (WhittakerBlock.archDeriv pq.1 pq.2 (word (fun x => ∑ i, c i * f (x * t i)) w)) y₁ y₂ k
      rw [Fintype.sum_prod_type'
        (fun p q => wnorm (WhittakerBlock.archDeriv p q (word (fun x => ∑ i, c i * f (x * t i)) w)) y₁ y₂ k)]
      exact (hcg k hk y₁ y₂ hy₁ hy₂).2)
    (fun y₁ _ => 1 * y₁ ^ m₁) (fun y₁ _ hy₁ _ => mul_nonneg zero_le_one (pow_nonneg hy₁.le m₁)) (run₁ m₁)

  have h₀₀ := run₂ 0 0 []
  have h₀₁ := run₂ 0 (M + N') []
  have h₁₀ := run₂ (M + N') 0 []
  have h₁₁ := run₂ (M + N') (M + N') []
  obtain ⟨C₀₀, h₀₀⟩ := h₀₀
  obtain ⟨C₀₁, h₀₁⟩ := h₀₁
  obtain ⟨C₁₀, h₁₀⟩ := h₁₀
  obtain ⟨C₁₁, h₁₁⟩ := h₁₁
  refine ⟨|C₀₀| + |C₀₁| + |C₁₀| + |C₁₁|, fun k hk a ha => ?_⟩
  have hy₁ : 0 < a 0 / a 1 := div_pos (ha 0) (ha 1)
  have hy₂ : 0 < a 1 / a 2 := div_pos (ha 1) (ha 2)
  have hG₁ : 0 ≤ min ((a 0 / a 1) ^ θ) ((a 0 / a 1) ^ (-(M : ℝ))) :=
    le_min (Real.rpow_nonneg hy₁.le _) (Real.rpow_nonneg hy₁.le _)
  have hG₂ : 0 ≤ min ((a 1 / a 2) ^ θ) ((a 1 / a 2) ^ (-(M : ℝ))) :=
    le_min (Real.rpow_nonneg hy₂.le _) (Real.rpow_nonneg hy₂.le _)
  have hGG := mul_nonneg hG₁ hG₂
  have h0 := abs_nonneg C₀₀
  have h1 := abs_nonneg C₀₁
  have h2 := abs_nonneg C₁₀
  have h3 := abs_nonneg C₁₁
  rw [norm_whittaker3_diag_mul_eq ω hω (fun x => ∑ i, c i * f (x * t i))
    (cen_sum_translate ω f hcen c t) a ha k, mul_assoc]
  show wnorm (word (fun x => ∑ i, c i * f (x * t i)) []) (a 0 / a 1) (a 1 / a 2) k ≤ _
  rcases le_or_gt (a 0 / a 1) 1 with hr₁ | hr₁ <;> rcases le_or_gt (a 1 / a 2) 1 with hr₂ | hr₂
  · exact (le_of_regimes (pow_pos hy₁ _) (pow_pos hy₂ _) (hF _ hy₁) (hF _ hy₂) hG₁ (h₀₀ k hk _ _ hy₁ hy₂)
      (regime_le_one hθp M N' hy₁ hr₁) (regime_le_one hθp M N' hy₂ hr₂)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hGG)
  · exact (le_of_regimes (pow_pos hy₁ _) (pow_pos hy₂ _) (hF _ hy₁) (hF _ hy₂) hG₁ (h₀₁ k hk _ _ hy₁ hy₂)
      (regime_le_one hθp M N' hy₁ hr₁) (regime_one_lt hθp M N' hy₂ hr₂)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hGG)
  · exact (le_of_regimes (pow_pos hy₁ _) (pow_pos hy₂ _) (hF _ hy₁) (hF _ hy₂) hG₁ (h₁₀ k hk _ _ hy₁ hy₂)
      (regime_one_lt hθp M N' hy₁ hr₁) (regime_le_one hθp M N' hy₂ hr₂)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hGG)
  · exact (le_of_regimes (pow_pos hy₁ _) (pow_pos hy₂ _) (hF _ hy₁) (hF _ hy₂) hG₁ (h₁₁ k hk _ _ hy₁ hy₂)
      (regime_one_lt hθp M N' hy₁ hr₁) (regime_one_lt hθp M N' hy₂ hr₂)).trans
      (mul_le_mul_of_nonneg_right (by linarith) hGG)

end S_LanglandsTunnell_CubicInduction_norm_whittaker3_sum_translate_diag_le_of_forall_rayOrder
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_norm_whittaker3_sum_translate_diag_le_of_forall_rayOrder (solution)
