-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isFundamentalDomain_mirabolic_and_lintegral_domainMeasure_eq_mul_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d8472168-dd98-581e-bb43-19fb867abbcd

import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Theorems.Thm_LanglandsTunnell_CubicInduction_measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc
import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_ideleNorm_archIdele
import Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_ideleNorm_det_centralScalarGL_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isFundamentalDomain_mirabolic_and_lintegral_domainMeasure_eq_mul_lintegral
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level"

set_option autoImplicit false

open scoped Pointwise ENNReal
open scoped ENNReal
open NumberField LanglandsTunnell.CubicInduction
open MeasureTheory NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open MeasureTheory NumberField NumberField.TateGlobal LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicInduction.SlabL2
open NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open scoped ENNReal Pointwise
open MeasureTheory NumberField LanglandsTunnell.CubicInduction

attribute [local instance] NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] LanglandsTunnell.CubicInduction.AdelicEpstein.unitIdeleMeasurableSpace
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

noncomputable section

namespace MirabolicUnfolding

private theorem row_mul_eq_of_row_eq_single {R n : Type*} [NonAssocSemiring R] [Fintype n] [DecidableEq n] (i : n)
    (P H : Matrix n n R) (hP : (fun j => P i j) = Pi.single i 1) :
    (fun j => (P * H) i j) = fun j => H i j :=
  calc (fun j => (P * H) i j) = Matrix.vecMul (fun j => P i j) H := rfl
    _ = Matrix.vecMul (Pi.single i 1) H := by rw [hP]
    _ = fun j => H i j := by
        rw [Matrix.single_one_vecMul]
        rfl

private theorem row_units_mul_eq_of_row_eq_single {R n : Type*} [Semiring R] [Fintype n] [DecidableEq n] (i : n)
    (p h : (Matrix n n R)ˣ) (hp : (fun j => (p : Matrix n n R) i j) = Pi.single i 1) :
    (fun j => ((p * h : (Matrix n n R)ˣ) : Matrix n n R) i j) = fun j => (h : Matrix n n R) i j := by
  rw [Units.val_mul]
  exact row_mul_eq_of_row_eq_single i _ _ hp

private theorem isFundamentalDomain_iUnion_smul_of_le
    {G α ι : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
    {μ : MeasureTheory.Measure α} [Countable ι] {Γ' Γ : Subgroup G} [MeasureTheory.SMulInvariantMeasure Γ α μ]
    (hle : Γ' ≤ Γ) {Ω₀ : Set α} (hΩ₀ : MeasureTheory.IsFundamentalDomain Γ Ω₀ μ)
    (ρ : ι → G) (hρ : ∀ i, ρ i ∈ Γ) (huniq : ∀ γ ∈ Γ, ∃! i, ρ i * γ ∈ Γ') :
    MeasureTheory.IsFundamentalDomain Γ' (⋃ i, ρ i • Ω₀) μ := by

  have hidx : ∀ i j, ρ i * (ρ j)⁻¹ ∈ Γ' → i = j := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := huniq (ρ j)⁻¹ (inv_mem (hρ j))
    have hj : ρ j * (ρ j)⁻¹ ∈ Γ' := by
      rw [mul_inv_cancel]
      exact one_mem _
    exact (hk i hij).trans (hk j hj).symm
  have hset : ∀ i, ρ i • Ω₀ = (⟨ρ i, hρ i⟩ : Γ) • Ω₀ := fun i => rfl
  refine ⟨?_, ?_, ?_⟩
  · refine MeasureTheory.NullMeasurableSet.iUnion fun i => ?_
    rw [hset i]
    exact hΩ₀.nullMeasurableSet_smul _
  · filter_upwards [hΩ₀.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    obtain ⟨i, hi, -⟩ := huniq (g : G) g.2
    refine ⟨⟨ρ i * (g : G), hi⟩, Set.mem_iUnion.2 ⟨i, ?_⟩⟩
    change (ρ i * (g : G)) • x ∈ ρ i • Ω₀
    rw [mul_smul]
    exact Set.smul_mem_smul_set hg
  · intro γ₁ γ₂ hne
    change MeasureTheory.AEDisjoint μ ((γ₁ : G) • ⋃ i, ρ i • Ω₀) ((γ₂ : G) • ⋃ i, ρ i • Ω₀)
    simp only [Set.smul_set_iUnion, smul_smul]
    refine MeasureTheory.AEDisjoint.iUnion_left_iff.2 fun i =>
      MeasureTheory.AEDisjoint.iUnion_right_iff.2 fun j => ?_
    have hm₁ : (γ₁ : G) * ρ i ∈ Γ := mul_mem (hle γ₁.2) (hρ i)
    have hm₂ : (γ₂ : G) * ρ j ∈ Γ := mul_mem (hle γ₂.2) (hρ j)
    by_cases hab : (γ₁ : G) * ρ i = (γ₂ : G) * ρ j
    ·
      exfalso
      have hρi : ρ i = (γ₁ : G)⁻¹ * ((γ₂ : G) * ρ j) := by
        rw [← hab, inv_mul_cancel_left]
      have hmem : ρ i * (ρ j)⁻¹ ∈ Γ' := by
        rw [hρi, mul_assoc, mul_inv_cancel_right]
        exact mul_mem (inv_mem γ₁.2) γ₂.2
      have hij : i = j := hidx i j hmem
      subst hij
      exact hne (Subtype.ext (mul_right_cancel hab))
    · have hne' : (⟨(γ₁ : G) * ρ i, hm₁⟩ : Γ) ≠ ⟨(γ₂ : G) * ρ j, hm₂⟩ :=
        fun h => hab (congrArg Subtype.val h)
      exact hΩ₀.aedisjoint hne'

private theorem setLIntegral_isFundamentalDomain_tsum_smul_eq
    {G α ι : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
    {μ : MeasureTheory.Measure α} [Countable ι] {Γ' Γ : Subgroup G} [MeasureTheory.SMulInvariantMeasure Γ α μ]
    {Ω₀ : Set α} (hΩ₀ : MeasureTheory.IsFundamentalDomain Γ Ω₀ μ)
    (ρ : ι → G) (hρ : ∀ i, ρ i ∈ Γ) (huniq : ∀ γ ∈ Γ, ∃! i, ρ i * γ ∈ Γ')
    {H : α → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ x in Ω₀, ∑' i, H (ρ i • x) ∂μ = ∫⁻ x in ⋃ i, ρ i • Ω₀, H x ∂μ := by
  have hidx : ∀ i j, ρ i * (ρ j)⁻¹ ∈ Γ' → i = j := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := huniq (ρ j)⁻¹ (inv_mem (hρ j))
    have hj : ρ j * (ρ j)⁻¹ ∈ Γ' := by
      rw [mul_inv_cancel]
      exact one_mem _
    exact (hk i hij).trans (hk j hj).symm
  have hset : ∀ i, ρ i • Ω₀ = (⟨ρ i, hρ i⟩ : Γ) • Ω₀ := fun i => rfl
  have hmeas : ∀ i, MeasureTheory.NullMeasurableSet (ρ i • Ω₀) μ := fun i => by
    rw [hset i]
    exact hΩ₀.nullMeasurableSet_smul _
  have hdisj : Pairwise (Function.onFun (MeasureTheory.AEDisjoint μ) fun i => ρ i • Ω₀) := by
    intro i j hne
    have hne' : (⟨ρ i, hρ i⟩ : Γ) ≠ ⟨ρ j, hρ j⟩ := by
      intro h
      apply hne
      apply hidx i j
      rw [show ρ i = ρ j from congrArg Subtype.val h, mul_inv_cancel]
      exact one_mem _
    exact hΩ₀.aedisjoint hne'
  have hmeasH : ∀ i, AEMeasurable (fun x => H (ρ i • x)) (μ.restrict Ω₀) := fun i =>
    (hH.comp (measurable_const_smul (ρ i))).aemeasurable
  rw [MeasureTheory.lintegral_iUnion₀ hmeas hdisj, MeasureTheory.lintegral_tsum hmeasH]
  refine tsum_congr fun i => ?_
  have h := (MeasureTheory.measurePreserving_smul (⟨ρ i, hρ i⟩ : Γ) μ).setLIntegral_comp_emb
    (measurableEmbedding_const_smul (⟨ρ i, hρ i⟩ : Γ)) H Ω₀
  rw [Set.image_smul, ← hset i] at h
  exact h

private theorem smul_set_ae_eq_self_of_smulInvariantMeasure_restrict
    {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] [MeasurableConstSMul Γ α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.SMulInvariantMeasure Γ α μ] {T : Set α}
    (hT : MeasurableSet T) [MeasureTheory.SMulInvariantMeasure Γ α (μ.restrict T)] (γ : Γ) :
    γ • T =ᵐ[μ] T := by
  have key : ∀ c : Γ, μ (T \ c⁻¹ • T) = 0 := fun c => by
    have h := MeasureTheory.SMulInvariantMeasure.measure_preimage_smul (μ := μ.restrict T) c hT.compl
    rw [MeasureTheory.Measure.restrict_apply (hT.compl.preimage (measurable_const_smul c)),
      MeasureTheory.Measure.restrict_apply hT.compl, Set.compl_inter_self, MeasureTheory.measure_empty,
      Set.preimage_compl, Set.preimage_smul, Set.inter_comm, ← Set.diff_eq] at h
    exact h
  refine MeasureTheory.ae_eq_set.2 ⟨?_, ?_⟩
  · rw [show γ • T \ T = γ • (T \ γ⁻¹ • T) by rw [Set.smul_set_sdiff, smul_inv_smul],
      MeasureTheory.measure_smul]
    exact key γ
  · simpa only [inv_inv] using key γ⁻¹

private theorem isFundamentalDomain_smul_restrict_smul_of_forall_mul_eq_mul
    {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.SMulInvariantMeasure G α μ] {Γ : Subgroup G}
    {T Ω : Set α} (hT : MeasurableSet T) (hΩ : MeasureTheory.IsFundamentalDomain Γ Ω (μ.restrict T))
    (z : G) (hz : ∀ γ ∈ Γ, z * γ = γ * z) :
    MeasureTheory.IsFundamentalDomain Γ (z • Ω) (μ.restrict (z • T)) := by
  have hq : MeasureTheory.Measure.QuasiMeasurePreserving (MulAction.toPerm z).symm
      (μ.restrict (z • T)) (μ.restrict T) := by
    have h := (MeasureTheory.measurePreserving_smul z⁻¹ μ).restrict_preimage hT
    rw [Set.preimage_smul, inv_inv] at h
    exact h.quasiMeasurePreserving
  have hsemi : ∀ γ : Γ, Function.Semiconj (MulAction.toPerm z) (fun x : α => γ • x)
      (fun x : α => (Equiv.refl Γ γ) • x) := by
    intro γ x
    change z • ((γ : G) • x) = (γ : G) • (z • x)
    rw [smul_smul, smul_smul, hz γ γ.2]
  have key := hΩ.image_of_equiv (MulAction.toPerm z) hq (Equiv.refl Γ) hsemi
  have himg : (MulAction.toPerm z : α → α) '' Ω = z • Ω := rfl
  rw [himg] at key
  exact key

private theorem isFundamentalDomain_iUnion_inter_of_restrict
    {Γ α ι : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [Countable Γ] [Countable ι] {T Ω : ι → Set α}
    (hT : ∀ n, MeasurableSet (T n)) (hcover : ∀ᵐ x ∂μ, ∃ n, x ∈ T n)
    (hdisj : Pairwise (Function.onFun Disjoint T)) (hinv : ∀ (γ : Γ) (n : ι), γ • T n =ᵐ[μ] T n)
    (hΩ : ∀ n, MeasureTheory.IsFundamentalDomain Γ (Ω n) (μ.restrict (T n))) :
    MeasureTheory.IsFundamentalDomain Γ (⋃ n, Ω n ∩ T n) μ := by
  refine ⟨?_, ?_, ?_⟩
  · exact MeasureTheory.NullMeasurableSet.iUnion fun n =>
      (MeasureTheory.nullMeasurableSet_restrict (hT n).nullMeasurableSet).1 (hΩ n).nullMeasurableSet
  · have h1 : ∀ n, ∀ᵐ x ∂μ, x ∈ T n → ∃ γ : Γ, γ • x ∈ Ω n := fun n =>
      (MeasureTheory.ae_restrict_iff' (hT n)).1 (hΩ n).ae_covers
    have h2 : ∀ (γ : Γ) (n : ι), ∀ᵐ x ∂μ, x ∈ γ⁻¹ • T n ↔ x ∈ T n := fun γ n => (hinv γ⁻¹ n).mem_iff
    filter_upwards [hcover, MeasureTheory.ae_all_iff.2 h1,
      MeasureTheory.ae_all_iff.2 fun γ => MeasureTheory.ae_all_iff.2 (h2 γ)] with x hx hx1 hx2
    obtain ⟨n, hn⟩ := hx
    obtain ⟨γ, hγ⟩ := hx1 n hn
    exact ⟨γ, Set.mem_iUnion.2 ⟨n, hγ, Set.mem_inv_smul_set_iff.1 ((hx2 γ n).2 hn)⟩⟩
  · intro γ₁ γ₂ hne
    change MeasureTheory.AEDisjoint μ (γ₁ • ⋃ n, Ω n ∩ T n) (γ₂ • ⋃ n, Ω n ∩ T n)
    simp only [Set.smul_set_iUnion, Set.smul_set_inter]
    refine MeasureTheory.AEDisjoint.iUnion_left_iff.2 fun n =>
      MeasureTheory.AEDisjoint.iUnion_right_iff.2 fun m => ?_
    unfold MeasureTheory.AEDisjoint
    refine MeasureTheory.measure_mono_null
      (t := γ₁ • Ω n ∩ γ₂ • Ω m ∩ (γ₁ • T n ∩ γ₂ • T m)) (fun x hx => ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2, hx.2.2⟩) ?_
    rw [MeasureTheory.measure_congr (MeasureTheory.ae_eq_set_inter
      (MeasureTheory.ae_eq_refl (γ₁ • Ω n ∩ γ₂ • Ω m : Set α))
      (MeasureTheory.ae_eq_set_inter (hinv γ₁ n) (hinv γ₂ m)))]
    by_cases hnm : n = m
    · subst hnm
      rw [Set.inter_self, ← MeasureTheory.Measure.restrict_apply_eq_zero' (hT n)]
      exact (hΩ n).aedisjoint hne
    · rw [Set.disjoint_iff_inter_eq_empty.1 (hdisj hnm), Set.inter_empty, MeasureTheory.measure_empty]

private theorem setLIntegral_inv_Icc {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∫⁻ t in Set.Icc α β, ENNReal.ofReal t⁻¹ = ENNReal.ofReal (Real.log (β / α)) := by
  have hsub : Set.Icc α β ⊆ ({0}ᶜ : Set ℝ) := fun t ht h0 =>
    (hα.trans_le ht.1).ne' (Set.mem_singleton_iff.1 h0)
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => t⁻¹) (Set.Icc α β) :=
    (continuousOn_inv₀.mono hsub).integrableOn_compact isCompact_Icc
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc α β)] fun t : ℝ => t⁻¹ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun t ht => inv_nonneg.2 (hα.le.trans ht.1)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hαβ, integral_inv_of_pos hα (hα.trans_le hαβ)]

private theorem setOf_pos_and_pow_three_mul_mem_Icc {a b D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hD : 0 < D) :
    {t : ℝ | 0 < t ∧ t ^ 3 * D ∈ Set.Icc a b} = Set.Icc ((a / D) ^ (1 / 3 : ℝ)) ((b / D) ^ (1 / 3 : ℝ)) := by
  have hb : 0 < b := ha.trans_le hab
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hpow : ∀ t : ℝ, t ^ (3 : ℝ) = t ^ 3 := fun t => by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Icc, one_div]
  constructor
  · rintro ⟨ht, h1, h2⟩
    refine ⟨(Real.rpow_inv_le_iff_of_pos (div_pos ha hD).le ht.le h3).2 ?_,
      (Real.le_rpow_inv_iff_of_pos ht.le (div_pos hb hD).le h3).2 ?_⟩
    · rw [hpow, div_le_iff₀ hD]
      exact h1
    · rw [hpow, le_div_iff₀ hD]
      exact h2
  · rintro ⟨h1, h2⟩
    have ht : 0 < t := (Real.rpow_pos_of_pos (div_pos ha hD) _).trans_le h1
    refine ⟨ht, ?_, ?_⟩
    · have h1' := (Real.rpow_inv_le_iff_of_pos (div_pos ha hD).le ht.le h3).1 h1
      rw [hpow, div_le_iff₀ hD] at h1'
      exact h1'
    · have h2' := (Real.le_rpow_inv_iff_of_pos ht.le (div_pos hb hD).le h3).1 h2
      rw [hpow, le_div_iff₀ hD] at h2'
      exact h2'

private theorem log_rpow_div_rpow_one_div_three {a b D : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) :
    Real.log ((b / D) ^ (1 / 3 : ℝ) / (a / D) ^ (1 / 3 : ℝ)) = Real.log (b / a) / 3 := by
  rw [← Real.div_rpow (div_pos hb hD).le (div_pos ha hD).le, div_div_div_cancel_right₀ hD.ne',
    Real.log_rpow (div_pos hb ha), one_div, inv_mul_eq_div]

private theorem setLIntegral_inv_setOf_pow_three_mul_mem_Icc {a b D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hD : 0 < D) :
    ∫⁻ t in {t : ℝ | 0 < t ∧ t ^ 3 * D ∈ Set.Icc a b}, ENNReal.ofReal t⁻¹ =
      ENNReal.ofReal (Real.log (b / a) / 3) := by
  have hb : 0 < b := ha.trans_le hab
  have hle : (a / D) ^ (1 / 3 : ℝ) ≤ (b / D) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (div_pos ha hD).le (div_le_div_of_nonneg_right hab hD.le) (by norm_num)
  rw [setOf_pos_and_pow_three_mul_mem_Icc ha hab hD,
    setLIntegral_inv_Icc (Real.rpow_pos_of_pos (div_pos ha hD) _) hle, log_rpow_div_rpow_one_div_three ha hb hD]

private theorem setOf_pos_and_div_pow_three_mem_Icc {a b D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hD : 0 < D) :
    {t : ℝ | 0 < t ∧ D / t ^ 3 ∈ Set.Icc a b} = Set.Icc ((D / b) ^ (1 / 3 : ℝ)) ((D / a) ^ (1 / 3 : ℝ)) := by
  have hb : 0 < b := ha.trans_le hab
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hpow : ∀ t : ℝ, t ^ (3 : ℝ) = t ^ 3 := fun t => by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Icc, one_div]
  constructor
  · rintro ⟨ht, h1, h2⟩
    have ht3 : 0 < t ^ 3 := pow_pos ht 3
    refine ⟨(Real.rpow_inv_le_iff_of_pos (div_pos hD hb).le ht.le h3).2 ?_,
      (Real.le_rpow_inv_iff_of_pos ht.le (div_pos hD ha).le h3).2 ?_⟩
    · rw [hpow, div_le_iff₀ hb, mul_comm]
      exact (div_le_iff₀ ht3).1 h2
    · rw [hpow, le_div_iff₀ ha, mul_comm]
      exact (le_div_iff₀ ht3).1 h1
  · rintro ⟨h1, h2⟩
    have ht : 0 < t := (Real.rpow_pos_of_pos (div_pos hD hb) _).trans_le h1
    have ht3 : 0 < t ^ 3 := pow_pos ht 3
    refine ⟨ht, ?_, ?_⟩
    · have h2' := (Real.le_rpow_inv_iff_of_pos ht.le (div_pos hD ha).le h3).1 h2
      rw [hpow, le_div_iff₀ ha, mul_comm] at h2'
      exact (le_div_iff₀ ht3).2 h2'
    · have h1' := (Real.rpow_inv_le_iff_of_pos (div_pos hD hb).le ht.le h3).1 h1
      rw [hpow, div_le_iff₀ hb, mul_comm] at h1'
      exact (div_le_iff₀ ht3).2 h1'

private theorem log_rpow_div_rpow_one_div_three' {a b D : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) :
    Real.log ((D / a) ^ (1 / 3 : ℝ) / (D / b) ^ (1 / 3 : ℝ)) = Real.log (b / a) / 3 := by
  rw [← Real.div_rpow (div_pos hD ha).le (div_pos hD hb).le, div_div_div_cancel_left' _ _ hD.ne',
    Real.log_rpow (div_pos hb ha), one_div, inv_mul_eq_div]

private theorem setLIntegral_inv_setOf_div_pow_three_mem_Icc {a b D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hD : 0 < D) :
    ∫⁻ t in {t : ℝ | 0 < t ∧ D / t ^ 3 ∈ Set.Icc a b}, ENNReal.ofReal t⁻¹ =
      ENNReal.ofReal (Real.log (b / a) / 3) := by
  have hb : 0 < b := ha.trans_le hab
  have hle : (D / b) ^ (1 / 3 : ℝ) ≤ (D / a) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (div_pos hD hb).le (div_le_div_of_nonneg_left hD.le ha hab) (by norm_num)
  rw [setOf_pos_and_div_pow_three_mem_Icc ha hab hD,
    setLIntegral_inv_Icc (Real.rpow_pos_of_pos (div_pos hD hb) _) hle, log_rpow_div_rpow_one_div_three' ha hb hD]

private theorem exists_mem_preimage_Ico_mul_zpow {α : Type*} (f : α → ℝ) {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    {x : α} (hx : 0 < f x) : ∃ n : ℤ, x ∈ f ⁻¹' Set.Ico (a * r ^ n) (a * r ^ (n + 1)) := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow (div_pos hx ha) hr
  refine ⟨n, ?_, ?_⟩
  · rw [mul_comm a]
    exact (le_div_iff₀ ha).1 hn1
  · rw [mul_comm a]
    exact (div_lt_iff₀ ha).1 hn2

private theorem pairwise_disjoint_Ico_mul_zpow_real {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    Pairwise (Function.onFun Disjoint fun n : ℤ => Set.Ico (a * r ^ n) (a * r ^ (n + 1))) := by
  intro m n hmn
  change Disjoint (Set.Ico (a * r ^ m) (a * r ^ (m + 1))) (Set.Ico (a * r ^ n) (a * r ^ (n + 1)))
  rcases lt_or_gt_of_ne hmn with h | h
  · refine Set.disjoint_left.2 fun x hxm hxn => ?_
    have hle : a * r ^ (m + 1) ≤ a * r ^ n :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hr.le (Int.lt_iff_add_one_le.1 h)) ha.le
    exact lt_irrefl x (hxm.2.trans_le (hle.trans hxn.1))
  · refine Set.disjoint_left.2 fun x hxm hxn => ?_
    have hle : a * r ^ (n + 1) ≤ a * r ^ m :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hr.le (Int.lt_iff_add_one_le.1 h)) ha.le
    exact lt_irrefl x (hxn.2.trans_le (hle.trans hxm.1))

private theorem pairwise_disjoint_preimage_Ico_mul_zpow {α : Type*} (f : α → ℝ) {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    Pairwise (Function.onFun Disjoint fun n : ℤ => f ⁻¹' Set.Ico (a * r ^ n) (a * r ^ (n + 1))) := by
  intro m n hmn
  change Disjoint (f ⁻¹' Set.Ico (a * r ^ m) (a * r ^ (m + 1))) (f ⁻¹' Set.Ico (a * r ^ n) (a * r ^ (n + 1)))
  exact Disjoint.preimage f (pairwise_disjoint_Ico_mul_zpow_real ha hr hmn)

private theorem iUnion_preimage_Ico_mul_zpow {α : Type*} (f : α → ℝ) {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    ⋃ n : ℤ, f ⁻¹' Set.Ico (a * r ^ n) (a * r ^ (n + 1)) = f ⁻¹' Set.Ioi 0 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_Ico, Set.mem_Ioi]
  constructor
  · rintro ⟨n, hn, -⟩
    exact (mul_pos ha (zpow_pos (zero_lt_one.trans hr) n)).trans_le hn
  · intro hx
    obtain ⟨n, hn⟩ := exists_mem_preimage_Ico_mul_zpow f ha hr hx
    exact ⟨n, hn⟩

private theorem measurable_coe_archIdele :
    Measurable fun t : ℝ =>
      ((LanglandsTunnell.CubicInduction.AdelicEpstein.archIdele t :
        (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
          NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) := by
  classical

  have hof : Continuous LanglandsTunnell.CubicInduction.AdelicEpstein.ofReal :=
    (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous

  let G : ℝ → NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ := fun t =>
    (Function.update (1 : NumberField.InfiniteAdeleRing ℚ) Rat.infinitePlace
      (LanglandsTunnell.CubicInduction.AdelicEpstein.ofReal t),
      (1 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
  have hG : Continuous G := (continuous_const.update Rat.infinitePlace hof).prodMk continuous_const
  have heq : (fun t : ℝ =>
      ((LanglandsTunnell.CubicInduction.AdelicEpstein.archIdele t :
        (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
          NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) =
      fun t : ℝ => if t = 0 then (1 : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) else G t := by
    funext t
    by_cases ht : t = 0
    · subst ht
      rw [if_pos rfl, LanglandsTunnell.CubicInduction.AdelicEpstein.archIdele, dif_pos rfl, Units.val_one]
    · rw [if_neg ht, LanglandsTunnell.CubicInduction.AdelicEpstein.archIdele, dif_neg ht,
        NumberField.TateGlobal.archUnitHom_apply]
      refine Prod.ext (funext fun v => ?_) (NumberField.AdelicVolume.archCentralUnit_snd _ _)
      by_cases hv : v = Rat.infinitePlace
      · subst hv
        rw [NumberField.AdelicVolume.archCentralUnit_fst_self]
        show LanglandsTunnell.CubicInduction.AdelicEpstein.ofReal t =
          Function.update (1 : NumberField.InfiniteAdeleRing ℚ) Rat.infinitePlace
            (LanglandsTunnell.CubicInduction.AdelicEpstein.ofReal t) Rat.infinitePlace
        rw [Function.update_self]
      · rw [NumberField.AdelicVolume.archCentralUnit_fst_of_ne _ _ hv]
        show (1 : v.Completion) =
          Function.update (1 : NumberField.InfiniteAdeleRing ℚ) Rat.infinitePlace
            (LanglandsTunnell.CubicInduction.AdelicEpstein.ofReal t) v
        rw [Function.update_of_ne hv]
        rfl
  rw [heq]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const hG.measurable

private theorem measurable_ennnorm_comp_point_generic
    [SecondCountableTopology (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)]
    (harch : Measurable fun t : ℝ =>
      ((LanglandsTunnell.CubicInduction.AdelicEpstein.archIdele t :
        (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
          NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
    {Φ : (Fin 3 → NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) → ℂ} (hΦ : Measurable Φ)
    (ξ : Fin 3 → ℚ) :
    Measurable fun p : (LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ × ℝ) ×
        IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ =>
      (‖Φ (LanglandsTunnell.CubicInduction.AdelicEpstein.point p.1.2 p.2 p.1.1 ξ)‖₊ : ℝ≥0∞) := by

  have h1 : Measurable fun p : (LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ × ℝ) ×
      IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ =>
        ((LanglandsTunnell.CubicInduction.AdelicEpstein.archIdele p.1.2 :
          (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
            NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :=
    harch.comp (measurable_snd.comp measurable_fst)
  have h2 : Measurable fun p : (LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ × ℝ) ×
      IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ =>
        ((LanglandsTunnell.CubicInduction.AdelicEpstein.finUnitIdele p.2 :
          (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
            NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :=
    LanglandsTunnell.CubicInduction.AdelicEpstein.measurable_finUnitIdele.comp measurable_snd
  have h3 : ∀ i : Fin 3, Measurable fun p :
      (LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ × ℝ) ×
        IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ =>
        Matrix.vecMul (LanglandsTunnell.CubicInduction.AdelicEpstein.adelicDiag ξ)
          (p.1.1 : Matrix (Fin 3) (Fin 3) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) i := by
    intro i
    exact ((continuous_apply i).comp (continuous_const.matrix_vecMul Units.continuous_val)).measurable.comp
      (measurable_fst.comp measurable_fst)

  have hpt : Measurable fun p : (LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ × ℝ) ×
      IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ =>
        LanglandsTunnell.CubicInduction.AdelicEpstein.point p.1.2 p.2 p.1.1 ξ := by
    refine measurable_pi_lambda _ fun i => ?_
    simp only [LanglandsTunnell.CubicInduction.AdelicEpstein.point, Units.val_mul]
    exact (h1.mul h2).mul (h3 i)
  exact (hΦ.comp hpt).nnnorm.coe_nnreal_ennreal

private theorem secondCountableTopology_gl3_of_adeleRing_secondCountable :
    SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdeleRing.secondCountableTopology ℚ
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private scoped instance sfinite_adelicGLHaar_gl3 :
    MeasureTheory.SFinite (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI := secondCountableTopology_gl3_of_adeleRing_secondCountable
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  infer_instance

private theorem exists_row_two_eq_of_ne_zero (v : Fin 3 → ℚ) (hv : v ≠ 0) :
    ∃ γ : GL (Fin 3) ℚ, (fun j : Fin 3 => (γ : Matrix (Fin 3) (Fin 3) ℚ) 2 j) = v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  rw [Pi.zero_apply] at hi
  fin_cases i
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1, 0; 0, 0, 1; v 0, v 1, v 2] ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simpa using hi
    · funext j
      fin_cases j <;> rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0, 0; 0, 0, 1; v 0, v 1, v 2] ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simpa using hi
    · funext j
      fin_cases j <;> rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0, 0; 0, 1, 0; v 0, v 1, v 2] ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simpa using hi
    · funext j
      fin_cases j <;> rfl

private theorem mem_closure_setOf_row_two_eq_single_iff (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    g ∈ Subgroup.closure
        {h : AdelicGL 3 (𝓞 ℚ) ℚ |
          (fun j : Fin 3 => (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) = Pi.single 2 1}
      ↔ (fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) = Pi.single 2 1 := by

  have key : ∀ h : AdelicGL 3 (𝓞 ℚ) ℚ,
      (fun j : Fin 3 => (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) = Pi.single 2 1 ↔
        Matrix.vecMul (Pi.single 2 1) (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = Pi.single 2 1 := by
    intro h
    rw [Matrix.single_one_vecMul]
    rfl
  let S : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ) :=
    { carrier := {h | (fun j : Fin 3 => (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) = Pi.single 2 1}
      one_mem' := by
        show (fun j : Fin 3 => ((1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j)
          = Pi.single 2 1
        rw [key]
        simp
      mul_mem' := by
        intro x y hx hy
        rw [Set.mem_setOf_eq, key] at hx hy ⊢
        rw [Units.val_mul, ← Matrix.vecMul_vecMul, hx, hy]
      inv_mem' := by
        intro x hx
        rw [Set.mem_setOf_eq, key] at hx ⊢
        calc Matrix.vecMul (Pi.single 2 1) ((x⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
            = Matrix.vecMul (Matrix.vecMul (Pi.single 2 1) (x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))
                ((x⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by rw [hx]
          _ = Pi.single 2 1 := by
                rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] }
  constructor
  · intro hg
    exact (Subgroup.closure_le S).2 (fun h hh => hh) hg
  · intro hg
    exact Subgroup.subset_closure hg

private scoped instance smulInvariantMeasure_range_restrict_setOf_ideleNorm_det_mem_Icc (s t : ℝ) :
    SMulInvariantMeasure (globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ)
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc s t}) := by
  refine ⟨fun c A hA => ?_⟩
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 c.2
  have hw := measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc s t γ
  have hfun : (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => c • x) = fun x => globalPointsGL 3 (𝓞 ℚ) ℚ γ * x := by
    funext x
    rw [Subgroup.smul_def, smul_eq_mul, hγ]
  rw [hfun]
  exact hw.measure_preimage hA.nullMeasurableSet

private theorem nnnorm_apply_centralScalar_mul_of_mem_automorphicSubmodule
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ automorphicSubmodule ω a b Φ₀)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ‖F (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)‖₊ = ‖F g‖₊ := by
  rw [((mem_automorphicSubmodule_iff ω a b Φ₀ F).1 hF).2.1 z g, nnnorm_mul]
  have h1 : ‖(ω z : ℂ)‖₊ = 1 := by
    ext
    simp [hω z]
  rw [h1, one_mul]

private theorem ideleNorm_det_globalPointsGL_eq_one (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ)) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap ℚ (Matrix.GeneralLinearGroup.det γ)
  have h2 : Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ) =
      Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) :=
    Matrix.GeneralLinearGroup.map_det (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) γ
  unfold ideleNorm
  rw [h2, h]
  simp

private theorem ideleNorm_det_globalPointsGL_mul (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ * h)) =
      ideleNorm ℚ (Matrix.GeneralLinearGroup.det h) := by
  rw [map_mul, ideleNorm_mul, ideleNorm_det_globalPointsGL_eq_one, one_mul]

private scoped instance borelSpace_adeleRing : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := ⟨rfl⟩

private theorem continuous_ideleNorm_det_gl3 :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
  refine (continuous_ideleNorm ℚ).comp (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact Units.continuous_val.matrix_det.congr fun g => (Matrix.GeneralLinearGroup.val_det_apply g).symm
  · exact Units.continuous_coe_inv.matrix_det.congr fun g => by
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]

private theorem measurable_ideleNorm_det :
    Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) :=
  continuous_ideleNorm_det_gl3.measurable

private def rowTwo (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Fin 3 → AdeleRing (𝓞 ℚ) ℚ :=
  fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j

private theorem continuous_rowTwo : Continuous rowTwo :=
  continuous_pi fun j => Units.continuous_val.matrix_elem 2 j

private theorem measurable_rowTwo : Measurable rowTwo :=
  measurable_pi_lambda _ fun j => (Units.continuous_val.matrix_elem 2 j).measurable

private def rhsIntegrand (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  (‖F g‖₊ : ℝ≥0∞) ^ 2 * (‖Φ (rowTwo g)‖₊ : ℝ≥0∞) *
    ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ)

private def scalarOf (t : ℝ) (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  centralScalarGL 3 (𝓞 ℚ) ℚ (AdelicEpstein.archIdele t * AdelicEpstein.finUnitIdele u)

private def orbitFn (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ) (t : ℝ)
    (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  (‖F h‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det h) ^ σ) *
    (ENNReal.ofReal (t ^ (3 * σ)) * (‖Φ (rowTwo (scalarOf t u * h))‖₊ : ℝ≥0∞))

private theorem measurable_nnnorm_sq {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : Continuous F) :
    Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (‖F g‖₊ : ℝ≥0∞) ^ 2 :=
  hF.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2

private theorem measurable_ofReal_ideleNorm_det_rpow (σ : ℝ) :
    Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ => ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) :=
  ENNReal.measurable_ofReal.comp (Measurable.pow_const measurable_ideleNorm_det σ)

private theorem measurable_ennnorm_comp_rowTwo {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Measurable Φ)
    (z : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Measurable fun h : AdelicGL 3 (𝓞 ℚ) ℚ => (‖Φ (rowTwo (z * h))‖₊ : ℝ≥0∞) :=
  (hΦ.comp (measurable_rowTwo.comp (measurable_const_mul z))).nnnorm.coe_nnreal_ennreal

private theorem measurable_rhsIntegrand {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : Continuous F)
    {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Measurable Φ) (σ : ℝ) : Measurable (rhsIntegrand F Φ σ) := by
  unfold rhsIntegrand
  exact ((measurable_nnnorm_sq hF).mul (hΦ.comp measurable_rowTwo).nnnorm.coe_nnreal_ennreal).mul
    (measurable_ofReal_ideleNorm_det_rpow σ)

private theorem rhsIntegrand_ne_top (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : rhsIntegrand F Φ σ g ≠ ⊤ := by
  unfold rhsIntegrand
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) ENNReal.coe_ne_top)
    ENNReal.ofReal_ne_top

private theorem measurable_orbitFn {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : Continuous F)
    {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Measurable Φ) (σ t : ℝ)
    (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) : Measurable (orbitFn F Φ σ t u) := by
  unfold orbitFn
  exact ((measurable_nnnorm_sq hF).mul (measurable_ofReal_ideleNorm_det_rpow σ)).mul
    (measurable_const.mul (measurable_ennnorm_comp_rowTwo hΦ (scalarOf t u)))

private noncomputable def rowRep (v : {v : Fin 3 → ℚ // v ≠ 0}) : Matrix.GeneralLinearGroup (Fin 3) ℚ :=
  Classical.choose (exists_row_two_eq_of_ne_zero v.1 v.2)

private theorem rowRep_row_two (v : {v : Fin 3 → ℚ // v ≠ 0}) :
    (fun j : Fin 3 => (rowRep v : Matrix (Fin 3) (Fin 3) ℚ) 2 j) = v.1 :=
  Classical.choose_spec (exists_row_two_eq_of_ne_zero v.1 v.2)

private theorem globalPointsGL_apply_row_two (M : Matrix.GeneralLinearGroup (Fin 3) ℚ) (i : Fin 3) :
    (globalPointsGL 3 (𝓞 ℚ) ℚ M : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 i =
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((M : Matrix (Fin 3) (Fin 3) ℚ) 2 i) :=
  Matrix.GeneralLinearGroup.map_apply (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) 2 i M

private theorem row_two_centralScalarGL_mul (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (j : Fin 3) :
    (centralScalarGL 3 (𝓞 ℚ) ℚ z * h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j =
      (z : AdeleRing (𝓞 ℚ) ℚ) * (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j := by
  change ((Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ)) * (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) 2 j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_mul]

private theorem row_two_globalPointsGL_mul (ρ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (j : Fin 3) :
    (globalPointsGL 3 (𝓞 ℚ) ℚ ρ * g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j =
      Matrix.vecMul (fun i : Fin 3 => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((ρ : Matrix (Fin 3) (Fin 3) ℚ) 2 i))
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) j := by
  rw [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [globalPointsGL_apply_row_two]

private theorem point_eq_row_two_centralScalarGL_mul_rowRep_mul (t : ℝ)
    (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}) :
    AdelicEpstein.point t u g ξ.1 =
      fun j : Fin 3 =>
        (centralScalarGL 3 (𝓞 ℚ) ℚ (AdelicEpstein.archIdele t * AdelicEpstein.finUnitIdele u) *
            ((globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep ξ) * g : AdelicGL 3 (𝓞 ℚ) ℚ) :
              Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j := by
  funext j
  rw [row_two_centralScalarGL_mul, Units.val_mul (globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep ξ)) g, row_two_globalPointsGL_mul]
  have hrow : (fun i : Fin 3 => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((rowRep ξ : Matrix (Fin 3) (Fin 3) ℚ) 2 i)) =
      AdelicEpstein.adelicDiag ξ.1 := by
    funext i
    have h2 : (rowRep ξ : Matrix (Fin 3) (Fin 3) ℚ) 2 i = ξ.1 i := congrFun (rowRep_row_two ξ) i
    simp only [AdelicEpstein.adelicDiag, h2]
  rw [hrow]
  rfl

private theorem nnnorm_apply_point_eq (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (t : ℝ)
    (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}) :
    (‖Φ (AdelicEpstein.point t u g ξ.1)‖₊ : ENNReal) =
      (fun h : AdelicGL 3 (𝓞 ℚ) ℚ =>
          (‖Φ (fun j : Fin 3 =>
            (centralScalarGL 3 (𝓞 ℚ) ℚ (AdelicEpstein.archIdele t * AdelicEpstein.finUnitIdele u) * h :
              Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j)‖₊ : ENNReal))
        ((⟨globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep ξ), MonoidHom.mem_range.2 ⟨rowRep ξ, rfl⟩⟩ :
            (globalPointsGL 3 (𝓞 ℚ) ℚ).range) • g) := by
  rw [point_eq_row_two_centralScalarGL_mul_rowRep_mul]
  rfl

private theorem row_two_mul_eq_vecMul {R : Type} [CommRing R] (A B : Matrix (Fin 3) (Fin 3) R) :
    (A * B) 2 = Matrix.vecMul (A 2) B := by
  funext j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

private theorem row_two_globalPointsGL (M : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    (fun j : Fin 3 => (globalPointsGL 3 (𝓞 ℚ) ℚ M : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
      fun j : Fin 3 => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((M : Matrix (Fin 3) (Fin 3) ℚ) 2 j) := by
  funext j
  exact Matrix.GeneralLinearGroup.map_apply (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) 2 j M

private theorem algebraMap_row_eq_single_iff (r : Fin 3 → ℚ) :
    (fun j : Fin 3 => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (r j)) = (Pi.single 2 1 : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) ↔
      r = Pi.single 2 1 := by
  haveI : Nontrivial (AdeleRing (𝓞 ℚ) ℚ) :=
    inferInstanceAs (Nontrivial (InfiniteAdeleRing ℚ × IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
  have hinj : Function.Injective (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) := (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).injective
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    apply hinj
    rw [hj]
    by_cases hj2 : j = 2
    · subst hj2; simp
    · simp [hj2]
  · intro h
    subst h
    funext j
    by_cases hj2 : j = 2
    · subst hj2; simp
    · simp [hj2]

private theorem existsUnique_mul_mem_mirabolic_of_row_two
    (ρ : {v : Fin 3 → ℚ // v ≠ 0} → Matrix.GeneralLinearGroup (Fin 3) ℚ)
    (hρ : ∀ v, (fun j : Fin 3 => (ρ v : Matrix (Fin 3) (Fin 3) ℚ) 2 j) = v.1) :
    ∀ γ ∈ (globalPointsGL 3 (𝓞 ℚ) ℚ).range, ∃! v, globalPointsGL 3 (𝓞 ℚ) ℚ (ρ v) * γ ∈
      Subgroup.closure
          {g : AdelicGL 3 (𝓞 ℚ) ℚ |
            (fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) = Pi.single 2 1} ⊓
        (globalPointsGL 3 (𝓞 ℚ) ℚ).range := by
  rintro γ ⟨γ₀, rfl⟩

  have hmem : ∀ v : {v : Fin 3 → ℚ // v ≠ 0},
      globalPointsGL 3 (𝓞 ℚ) ℚ (ρ v) * globalPointsGL 3 (𝓞 ℚ) ℚ γ₀ ∈
        Subgroup.closure
            {g : AdelicGL 3 (𝓞 ℚ) ℚ |
              (fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) = Pi.single 2 1} ⊓
          (globalPointsGL 3 (𝓞 ℚ) ℚ).range ↔
        Matrix.vecMul v.1 (γ₀ : Matrix (Fin 3) (Fin 3) ℚ) = Pi.single 2 1 := by
    intro v
    have hρ' : (ρ v : Matrix (Fin 3) (Fin 3) ℚ) 2 = v.1 := hρ v
    rw [Subgroup.mem_inf, ← map_mul, mem_closure_setOf_row_two_eq_single_iff, row_two_globalPointsGL,
      Units.val_mul, algebraMap_row_eq_single_iff, row_two_mul_eq_vecMul, hρ']
    exact and_iff_left (MonoidHom.mem_range.2 ⟨ρ v * γ₀, rfl⟩)

  have hsol : ∀ r : Fin 3 → ℚ, Matrix.vecMul r (γ₀ : Matrix (Fin 3) (Fin 3) ℚ) = Pi.single 2 1 ↔
      r = Matrix.vecMul (Pi.single 2 1 : Fin 3 → ℚ)
        ((γ₀⁻¹ : Matrix.GeneralLinearGroup (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) := by
    intro r
    constructor
    · intro h
      rw [← h, Matrix.vecMul_vecMul]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    · intro h
      rw [h, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have hne : Matrix.vecMul (Pi.single 2 1 : Fin 3 → ℚ)
      ((γ₀⁻¹ : Matrix.GeneralLinearGroup (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) ≠ 0 := by
    intro h0
    have h1 := (hsol _).2 rfl
    rw [h0, Matrix.zero_vecMul] at h1
    have h2 := congrFun h1 2
    simp at h2
  refine ⟨⟨_, hne⟩, (hmem _).2 ((hsol _).2 rfl), ?_⟩
  intro w hw
  exact Subtype.ext ((hsol _).1 ((hmem w).1 hw))

private def mirabolic : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  Subgroup.closure {g | (fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) = Pi.single 2 1} ⊓
    (globalPointsGL 3 (𝓞 ℚ) ℚ).range

private theorem existsUnique_rowRep_mul_mem_mirabolic :
    ∀ γ ∈ (globalPointsGL 3 (𝓞 ℚ) ℚ).range,
      ∃! v : {v : Fin 3 → ℚ // v ≠ 0}, globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v) * γ ∈ mirabolic :=
  existsUnique_mul_mem_mirabolic_of_row_two rowRep rowRep_row_two

private scoped instance smulInvariantMeasure_range_slabMeasure (a b : ℝ) :
    MeasureTheory.SMulInvariantMeasure (globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ) (slabMeasure a b) :=
  smulInvariantMeasure_range_restrict_setOf_ideleNorm_det_mem_Icc a b

private scoped instance measurableConstSMul_adelicGL :
    MeasurableConstSMul (AdelicGL 3 (𝓞 ℚ) ℚ) (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  inferInstance

private theorem mirabolic_le_range : mirabolic ≤ (globalPointsGL 3 (𝓞 ℚ) ℚ).range := inf_le_right

private scoped instance countable_mirabolic : Countable mirabolic := by
  haveI : Countable (Matrix (Fin 3) (Fin 3) ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 3 → ℚ))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 3) ℚ) := Function.Injective.countable Units.val_injective
  exact ((Set.countable_range (globalPointsGL 3 (𝓞 ℚ) ℚ)).mono
    fun x hx => MonoidHom.mem_range.1 (mirabolic_le_range hx)).to_subtype

private theorem globalPointsGL_rowRep_mem_range (v : {v : Fin 3 → ℚ // v ≠ 0}) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v) ∈ (globalPointsGL 3 (𝓞 ℚ) ℚ).range :=
  MonoidHom.mem_range.2 ⟨rowRep v, rfl⟩

private theorem isFundamentalDomain_mirabolic_iUnion (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hΦ₀ : IsSlabDomain a b Φ₀) :
    MeasureTheory.IsFundamentalDomain mirabolic
      (⋃ v : {v : Fin 3 → ℚ // v ≠ 0}, globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v) • Φ₀) (slabMeasure a b) :=
  isFundamentalDomain_iUnion_smul_of_le mirabolic_le_range hΦ₀.2.2 (fun v => globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v))
    globalPointsGL_rowRep_mem_range existsUnique_rowRep_mul_mem_mirabolic

private theorem setLIntegral_tsum_smul_eq (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    {H : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ g in Φ₀, ∑' v : {v : Fin 3 → ℚ // v ≠ 0}, H (globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v) • g) ∂(slabMeasure a b) =
      ∫⁻ h in ⋃ v : {v : Fin 3 → ℚ // v ≠ 0}, globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v) • Φ₀, H h ∂(slabMeasure a b) :=
  setLIntegral_isFundamentalDomain_tsum_smul_eq (Γ' := mirabolic) hΦ₀.2.2
    (fun v => globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v)) globalPointsGL_rowRep_mem_range
    existsUnique_rowRep_mul_mem_mirabolic hH

private theorem lintegral_scaleMeasure_congr (f₁ f₂ : ℝ → ℝ≥0∞) (h : ∀ t, 0 < t → f₁ t = f₂ t) :
    ∫⁻ t, f₁ t ∂AdelicEpstein.scaleMeasure = ∫⁻ t, f₂ t ∂AdelicEpstein.scaleMeasure := by
  unfold AdelicEpstein.scaleMeasure
  refine MeasureTheory.lintegral_congr_ae ?_
  have h1 : f₁ =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] f₂ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => h t ht)
  exact (MeasureTheory.withDensity_absolutelyContinuous _ _).ae_eq h1

private def slice (a b t : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {h | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det h) / t ^ 3 ∈ Set.Icc a b}

private def scalesOf (a b : ℝ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) : Set ℝ :=
  {t : ℝ | 0 < t ∧ NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det h) / t ^ 3 ∈ Set.Icc a b}

private theorem mem_slice_iff (a b t : ℝ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    h ∈ slice a b t ↔ NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det h) / t ^ 3 ∈ Set.Icc a b :=
  Iff.rfl

private theorem measurableSet_uncurry_slice (a b : ℝ) :
    MeasurableSet {p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ | p.2 ∈ slice a b p.1} := by
  have hf : Measurable fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det p.2) / p.1 ^ 3 :=
    (measurable_ideleNorm_det.comp measurable_snd).div (measurable_fst.pow_const 3)
  exact hf measurableSet_Icc

private theorem lintegral_scales_eq (a b : ℝ) (ha : 0 < a) (hab : a < b) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * (slice a b t).indicator (fun _ => (1 : ℝ≥0∞)) h =
      ENNReal.ofReal (Real.log (b / a) / 3) := by
  have hset : ∀ t : ℝ, (slice a b t).indicator (fun _ => (1 : ℝ≥0∞)) h = (scalesOf a b h ∩ Set.Ioi 0).indicator
      (fun _ => (1 : ℝ≥0∞)) t ∨ t ∉ Set.Ioi (0 : ℝ) := by
    intro t
    by_cases ht : 0 < t
    · left
      by_cases hmem : h ∈ slice a b t
      · have hmS : t ∈ scalesOf a b h ∩ Set.Ioi 0 := ⟨⟨ht, (mem_slice_iff a b t h).1 hmem⟩, ht⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmS]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem]
        rintro ⟨⟨-, hm⟩, -⟩
        exact hmem ((mem_slice_iff a b t h).2 hm)
    · exact Or.inr ht
  have hmeasS : MeasurableSet (scalesOf a b h) := by
    have hf : Measurable fun t : ℝ =>
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det h) / t ^ 3 :=
      measurable_const.div (measurable_id.pow_const 3)
    exact measurableSet_Ioi.inter (hf measurableSet_Icc)
  calc ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal t⁻¹ * (slice a b t).indicator (fun _ => (1 : ℝ≥0∞)) h
      = ∫⁻ t in Set.Ioi (0 : ℝ), (scalesOf a b h).indicator (fun t => ENNReal.ofReal t⁻¹) t := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rcases hset t with hs | hs
        · rw [hs]
          by_cases hm : t ∈ scalesOf a b h
          · have hmS : t ∈ scalesOf a b h ∩ Set.Ioi 0 := ⟨hm, ht⟩
            rw [Set.indicator_of_mem hmS, Set.indicator_of_mem hm, mul_one]
          · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun hm' => hm hm'.1), mul_zero]
        · exact absurd ht hs
    _ = ∫⁻ t in scalesOf a b h, ENNReal.ofReal t⁻¹ := by
        rw [← lintegral_indicator hmeasS, ← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun t => ?_
        by_cases hm : t ∈ scalesOf a b h
        · have ht0 : t ∈ Set.Ioi (0 : ℝ) := hm.1
          rw [Set.indicator_of_mem ht0, Set.indicator_of_mem hm]
        · rw [Set.indicator_of_notMem hm]
          by_cases ht : t ∈ Set.Ioi (0 : ℝ)
          · rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hm]
          · rw [Set.indicator_of_notMem ht]
    _ = ENNReal.ofReal (Real.log (b / a) / 3) :=
        setLIntegral_inv_setOf_div_pow_three_mem_Icc ha hab.le
          (NumberField.TateGlobal.ideleNorm_pos (Matrix.GeneralLinearGroup.det h))

private theorem lintegral_scaleMeasure_setLIntegral_indicator_slice (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Ω : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞) (hψ : Measurable ψ) (hψt : ∀ h, ψ h ≠ ⊤) :
    ∫⁻ t, ∫⁻ h in Ω, (slice a b t).indicator ψ h ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
        ∂AdelicEpstein.scaleMeasure =
      ENNReal.ofReal (Real.log (b / a) / 3) *
        ∫⁻ h in Ω, ψ h ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  set μ := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ

  have hw : Measurable fun t : ℝ => ENNReal.ofReal t⁻¹ := ENNReal.measurable_ofReal.comp measurable_inv
  unfold AdelicEpstein.scaleMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hw
    (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]

  have hsplit : ∀ (t : ℝ) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
      (slice a b t).indicator ψ h = ψ h * (slice a b t).indicator (fun _ => (1 : ℝ≥0∞)) h := by
    intro t h
    by_cases hm : h ∈ slice a b t
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, mul_one]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, mul_zero]

  have hjoint : Measurable fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
      ENNReal.ofReal p.1⁻¹ * (ψ p.2 * (slice a b p.1).indicator (fun _ => (1 : ℝ≥0∞)) p.2) := by
    have hind : Measurable fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
        (slice a b p.1).indicator (fun _ => (1 : ℝ≥0∞)) p.2 := by
      have : (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => (slice a b p.1).indicator (fun _ => (1 : ℝ≥0∞)) p.2) =
          {p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ | p.2 ∈ slice a b p.1}.indicator fun _ => (1 : ℝ≥0∞) := by
        funext p
        by_cases hm : p.2 ∈ slice a b p.1
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show p ∈ {p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ |
            p.2 ∈ slice a b p.1} from hm)]
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show p ∉ {p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ |
            p.2 ∈ slice a b p.1} from hm)]
      rw [this]
      exact measurable_const.indicator (measurableSet_uncurry_slice a b)
    exact (hw.comp measurable_fst).mul ((hψ.comp measurable_snd).mul hind)
  calc ∫⁻ t, ((fun t => ENNReal.ofReal t⁻¹) * fun t => ∫⁻ h in Ω, (slice a b t).indicator ψ h ∂μ) t
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))
      = ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ h in Ω,
          ENNReal.ofReal t⁻¹ * (ψ h * (slice a b t).indicator (fun _ => (1 : ℝ≥0∞)) h) ∂μ := by
        refine lintegral_congr fun t => ?_
        simp only [Pi.mul_apply]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun h => by rw [hsplit]
    _ = ∫⁻ h in Ω, (∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal t⁻¹ * (ψ h * (slice a b t).indicator (fun _ => (1 : ℝ≥0∞)) h)) ∂μ := by
        exact lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ h in Ω, ψ h * ENNReal.ofReal (Real.log (b / a) / 3) ∂μ := by
        refine lintegral_congr fun h => ?_
        rw [← lintegral_scales_eq a b ha hab h, ← lintegral_const_mul' _ _ ?_]
        · exact lintegral_congr fun t => by ring
        · exact hψt h
    _ = ENNReal.ofReal (Real.log (b / a) / 3) * ∫⁻ h in Ω, ψ h ∂μ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]

private theorem measurableSet_slice (a b t : ℝ) : MeasurableSet (slice a b t) := by
  unfold slice
  exact (measurable_ideleNorm_det.div_const (t ^ 3)) measurableSet_Icc

private theorem measurableSet_slab (a b : ℝ) :
    MeasurableSet {g : AdelicGL 3 (𝓞 ℚ) ℚ | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} :=
  continuous_ideleNorm_det_gl3.measurable measurableSet_Icc

private theorem ideleNorm_finUnitIdele (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) :
    ideleNorm ℚ (AdelicEpstein.finUnitIdele u) = 1 :=
  NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ _ rfl (by
    rw [show NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ (AdelicEpstein.finUnitIdele u) =
        (u : (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) from Units.ext rfl]
    exact u.2)

private theorem ideleNorm_det_scalarOf_mul (t : ℝ) (ht : 0 < t)
    (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (scalarOf t u * h)) =
      t ^ 3 * ideleNorm ℚ (Matrix.GeneralLinearGroup.det h) := by
  rw [scalarOf, LanglandsTunnell.CubicInduction.AdelicEpstein.ideleNorm_det_centralScalarGL_mul, ideleNorm_mul,
    LanglandsTunnell.CubicInduction.AdelicEpstein.ideleNorm_archIdele t ht, ideleNorm_finUnitIdele, mul_one]

private theorem rowTwo_mul_eq_of_mem_mirabolic {p : AdelicGL 3 (𝓞 ℚ) ℚ} (hp : p ∈ mirabolic)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) : rowTwo (p * h) = rowTwo h := by
  exact row_units_mul_eq_of_row_eq_single 2 p h
    ((mem_closure_setOf_row_two_eq_single_iff p).1 (Subgroup.mem_inf.1 hp).1)

private theorem centralScalarGL_mul_comm (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (p : AdelicGL 3 (𝓞 ℚ) ℚ) :
    centralScalarGL 3 (𝓞 ℚ) ℚ z * p = p * centralScalarGL 3 (𝓞 ℚ) ℚ z := by
  ext1
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 ℚ) ℚ) (fun r' => Commute.all _ r') _).eq

private theorem scalarOf_mul_comm (t : ℝ) (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)
    (p : AdelicGL 3 (𝓞 ℚ) ℚ) : scalarOf t u * p = p * scalarOf t u :=
  centralScalarGL_mul_comm _ p

private theorem smulInvariantMeasure_mirabolic (μ : Measure (AdelicGL 3 (𝓞 ℚ) ℚ))
    [MeasureTheory.SMulInvariantMeasure (globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ) μ] :
    MeasureTheory.SMulInvariantMeasure mirabolic (AdelicGL 3 (𝓞 ℚ) ℚ) μ :=
  ⟨fun p _ hs =>
    MeasureTheory.SMulInvariantMeasure.measure_preimage_smul (μ := μ)
      (⟨(p : AdelicGL 3 (𝓞 ℚ) ℚ), mirabolic_le_range p.2⟩ : (globalPointsGL 3 (𝓞 ℚ) ℚ).range) hs⟩

private theorem orbitFn_eq_rhsIntegrand_scalarOf_mul (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ automorphicSubmodule ω a b Φ₀) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    orbitFn F Φ σ t u h = rhsIntegrand F Φ σ (scalarOf t u * h) := by
  unfold orbitFn rhsIntegrand
  rw [show scalarOf t u * h = centralScalarGL 3 (𝓞 ℚ) ℚ (AdelicEpstein.archIdele t * AdelicEpstein.finUnitIdele u) * h
      from rfl, nnnorm_apply_centralScalar_mul_of_mem_automorphicSubmodule ω hω a b Φ₀ F hF,
    ← show scalarOf t u * h = centralScalarGL 3 (𝓞 ℚ) ℚ (AdelicEpstein.archIdele t * AdelicEpstein.finUnitIdele u) * h
      from rfl, ideleNorm_det_scalarOf_mul t ht u h,
    Real.mul_rpow (pow_nonneg ht.le 3) (ideleNorm_pos (Matrix.GeneralLinearGroup.det h)).le,
    ENNReal.ofReal_mul (Real.rpow_nonneg (pow_nonneg ht.le 3) σ), ← Real.rpow_natCast t 3,
    ← Real.rpow_mul ht.le]
  push_cast
  ring

private theorem setLIntegral_orbitFn_eq_setLIntegral_indicator_slice (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ automorphicSubmodule ω a b Φ₀)
    (hFinv : ∀ p ∈ mirabolic, ∀ g, ‖F (p * g)‖₊ = ‖F g‖₊) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    {Ω₁ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hΩ₁ : IsFundamentalDomain mirabolic Ω₁ (slabMeasure a b))
    {Ω : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hΩ : IsFundamentalDomain mirabolic Ω (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    {t : ℝ} (ht : 0 < t) (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) :
    ∫⁻ h in Ω₁, orbitFn F Φ σ t u h ∂(slabMeasure a b) =
      ∫⁻ h in Ω, (slice a b t).indicator (rhsIntegrand F Φ σ) h
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  set μ := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ with hμ
  set z := scalarOf t u with hz
  set ψ := rhsIntegrand F Φ σ with hψ
  set S : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} with hS
  have hS_meas : MeasurableSet S := measurableSet_slab a b
  have hT_meas : MeasurableSet (slice a b t) := measurableSet_slice a b t

  have hΩ₁' : IsFundamentalDomain mirabolic Ω₁ (μ.restrict S) := hΩ₁
  have hslice : z • S = slice a b t := by
    ext h
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
    have hmul := ideleNorm_det_scalarOf_mul t ht u (z⁻¹ * h)
    rw [← hz, mul_inv_cancel_left] at hmul
    show ideleNorm ℚ (Matrix.GeneralLinearGroup.det (z⁻¹ * h)) ∈ Set.Icc a b ↔
      ideleNorm ℚ (Matrix.GeneralLinearGroup.det h) / t ^ 3 ∈ Set.Icc a b
    rw [hmul, mul_div_cancel_left₀ _ (pow_pos ht 3).ne']

  have hslice' : slice a b t = {g : AdelicGL 3 (𝓞 ℚ) ℚ |
      ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (a * t ^ 3) (b * t ^ 3)} := by
    ext h
    have h3 : 0 < t ^ 3 := pow_pos ht 3
    simp only [slice, Set.mem_setOf_eq, Set.mem_Icc, le_div_iff₀ h3, div_le_iff₀ h3]
  haveI : MeasureTheory.SMulInvariantMeasure mirabolic (AdelicGL 3 (𝓞 ℚ) ℚ) (μ.restrict (slice a b t)) := by
    rw [hslice']
    exact smulInvariantMeasure_mirabolic _

  have hsub : ∀ X : Set (AdelicGL 3 (𝓞 ℚ) ℚ), ∫⁻ h in X, ψ (z * h) ∂μ = ∫⁻ h in z • X, ψ h ∂μ := by
    intro X
    have hpre := (measurePreserving_smul z μ).setLIntegral_comp_preimage_emb (measurableEmbedding_const_smul z) ψ
      (z • X)
    rwa [Set.preimage_smul, inv_smul_smul] at hpre
  calc ∫⁻ h in Ω₁, orbitFn F Φ σ t u h ∂(slabMeasure a b)
      = ∫⁻ h in Ω₁ ∩ S, ψ (z * h) ∂μ := by
        rw [show slabMeasure a b = μ.restrict S from rfl, Measure.restrict_restrict' hS_meas]
        exact lintegral_congr fun h => orbitFn_eq_rhsIntegrand_scalarOf_mul ω hω a b Φ₀ hF Φ σ ht u h
    _ = ∫⁻ h in z • Ω₁, ψ h ∂(μ.restrict (slice a b t)) := by

        rw [hsub, Set.smul_set_inter, hslice, Measure.restrict_restrict' hT_meas]
    _ = ∫⁻ h in Ω, ψ h ∂(μ.restrict (slice a b t)) := by

        have hzΩ : IsFundamentalDomain mirabolic (z • Ω₁) (μ.restrict (slice a b t)) := by
          rw [← hslice]
          exact isFundamentalDomain_smul_restrict_smul_of_forall_mul_eq_mul hS_meas hΩ₁' z
            fun p _ => scalarOf_mul_comm t u p
        have hΩ' : IsFundamentalDomain mirabolic Ω (μ.restrict (slice a b t)) :=
          hΩ.mono Measure.restrict_le_self.absolutelyContinuous
        refine hzΩ.setLIntegral_eq hΩ' ψ fun p h => ?_
        obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 (mirabolic_le_range p.2)
        simp only [hψ, rhsIntegrand, Subgroup.smul_def, smul_eq_mul, hFinv p.1 p.2, rowTwo_mul_eq_of_mem_mirabolic p.2]
        rw [← hγ, ideleNorm_det_globalPointsGL_mul]
    _ = ∫⁻ h in Ω, (slice a b t).indicator ψ h ∂μ := by

        rw [Measure.restrict_restrict' hT_meas, lintegral_indicator hT_meas, Measure.restrict_restrict hT_meas,
          Set.inter_comm]

private noncomputable def detNorm3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ :=
  NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)

private theorem detNorm3_pos (g : AdelicGL 3 (𝓞 ℚ) ℚ) : 0 < detNorm3 g :=
  NumberField.TateGlobal.ideleNorm_pos ..

private noncomputable def tileOf (a b : ℝ) (n : ℤ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  detNorm3 ⁻¹' Set.Ico (a * (b / a) ^ n) (a * (b / a) ^ (n + 1))

private theorem measurableSet_tileOf (a b : ℝ) (n : ℤ) : MeasurableSet (tileOf a b n) :=
  measurable_ideleNorm_det measurableSet_Ico

private noncomputable def scaleBy (s : ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  scalarOf s 1

private theorem detNorm3_scaleBy_mul {s : ℝ} (hs : 0 < s) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    detNorm3 (scaleBy s * g) = s ^ 3 * detNorm3 g :=
  ideleNorm_det_scalarOf_mul s hs 1 g

private theorem detNorm3_globalPointsGL_mul (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    detNorm3 (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = detNorm3 g :=
  ideleNorm_det_globalPointsGL_mul γ g

private scoped instance smulInvariantMeasure_adelicGLHaar :
    SMulInvariantMeasure (AdelicGL 3 (𝓞 ℚ) ℚ) (AdelicGL 3 (𝓞 ℚ) ℚ)
      (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
  ⟨fun z A _ => measure_preimage_mul (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) z A⟩

private theorem countable_of_le_range (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) (hP : P ≤ (globalPointsGL 3 (𝓞 ℚ) ℚ).range) :
    Countable P := by
  haveI : Countable (Matrix (Fin 3) (Fin 3) ℚ) := inferInstanceAs (Countable (Fin 3 → Fin 3 → ℚ))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 3) ℚ) := Function.Injective.countable Units.val_injective
  exact ((Set.countable_range (globalPointsGL 3 (𝓞 ℚ) ℚ)).mono
    fun x hx => MonoidHom.mem_range.1 (hP hx)).to_subtype

private theorem smul_tileOf_eq (a b : ℝ) {P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hP : P ≤ (globalPointsGL 3 (𝓞 ℚ) ℚ).range) (p : P) (n : ℤ) : p • tileOf a b n = tileOf a b n := by
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 (hP p.2)
  ext g
  rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv, ← hγ, ← map_inv]
  simp only [tileOf, Set.mem_preimage, detNorm3_globalPointsGL_mul]

private theorem tileOf_subset_scaleBy_smul_slab {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℤ) :
    tileOf a b n ⊆ scaleBy ((b / a) ^ ((n : ℝ) / 3)) • {g : AdelicGL 3 (𝓞 ℚ) ℚ | detNorm3 g ∈ Set.Icc a b} := by
  have hr : 0 < b / a := div_pos (ha.trans hab) ha
  set s : ℝ := (b / a) ^ ((n : ℝ) / 3) with hs_def
  have hs : 0 < s := Real.rpow_pos_of_pos hr _
  have hs3 : s ^ 3 = (b / a) ^ n := by
    rw [hs_def, ← Real.rpow_natCast, ← Real.rpow_mul hr.le,
      show (n : ℝ) / 3 * ((3 : ℕ) : ℝ) = (n : ℝ) by push_cast; ring, Real.rpow_intCast]
  have hrn : 0 < (b / a) ^ n := zpow_pos hr n
  intro g hg
  obtain ⟨hg₁, hg₂⟩ := hg
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

  have hdet : detNorm3 ((scaleBy s)⁻¹ * g) = detNorm3 g / (b / a) ^ n := by
    have h := detNorm3_scaleBy_mul hs ((scaleBy s)⁻¹ * g)
    rw [mul_inv_cancel_left, hs3] at h
    rw [eq_div_iff hrn.ne', mul_comm]
    exact h.symm
  show detNorm3 ((scaleBy s)⁻¹ * g) ∈ Set.Icc a b
  rw [hdet]
  constructor
  · rw [le_div_iff₀ hrn]; exact hg₁
  · rw [div_le_iff₀ hrn]
    calc detNorm3 g ≤ a * (b / a) ^ (n + 1) := hg₂.le
      _ = b * (b / a) ^ n := by
          rw [zpow_add_one₀ hr.ne']
          have ha' : a ≠ 0 := ha.ne'
          generalize (b / a) ^ n = q
          field_simp

private theorem exists_isFundamentalDomain_mirabolic_of_isSlabDomain (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hΦ₀ : IsSlabDomain a b Φ₀) (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ)) (hP : P ≤ (globalPointsGL 3 (𝓞 ℚ) ℚ).range)
    (Ω₁ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hΩ₁ : IsFundamentalDomain P Ω₁ ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict
      {g | detNorm3 g ∈ Set.Icc a b})) :
    ∃ Ω : Set (AdelicGL 3 (𝓞 ℚ) ℚ),
      IsFundamentalDomain P Ω (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  obtain ⟨ha, hab, -⟩ := hΦ₀
  have hr : 1 < b / a := (one_lt_div ha).2 hab
  haveI : Countable P := countable_of_le_range P hP
  have hcover : ∀ᵐ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ), ∃ n : ℤ, g ∈ tileOf a b n :=
    Filter.Eventually.of_forall fun g => exists_mem_preimage_Ico_mul_zpow detNorm3 ha hr (detNorm3_pos g)
  have hdisj : Pairwise (Function.onFun Disjoint (tileOf a b)) :=
    pairwise_disjoint_preimage_Ico_mul_zpow detNorm3 ha hr
  have hinv : ∀ (p : P) (n : ℤ),
      p • tileOf a b n =ᵐ[NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ] tileOf a b n :=
    fun p n => by rw [smul_tileOf_eq a b hP p n]
  have hΩn : ∀ n : ℤ, IsFundamentalDomain P (scaleBy ((b / a) ^ ((n : ℝ) / 3)) • Ω₁)
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict (tileOf a b n)) := by
    intro n
    have h1 := isFundamentalDomain_smul_restrict_smul_of_forall_mul_eq_mul (measurableSet_slab a b) hΩ₁
      (scaleBy ((b / a) ^ ((n : ℝ) / 3))) fun p _ => scalarOf_mul_comm ((b / a) ^ ((n : ℝ) / 3)) 1 p

    exact h1.mono (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (tileOf_subset_scaleBy_smul_slab ha hab n) le_rfl))
  exact ⟨⋃ n : ℤ, scaleBy ((b / a) ^ ((n : ℝ) / 3)) • Ω₁ ∩ tileOf a b n,
    isFundamentalDomain_iUnion_inter_of_restrict (measurableSet_tileOf a b) hcover hdisj hinv hΩn⟩

private scoped instance secondCountableTopology_adeleRing : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

private theorem measurable_ennnorm_comp_point {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Measurable Φ)
    (ξ : Fin 3 → ℚ) :
    Measurable fun p : (AdelicGL 3 (𝓞 ℚ) ℚ × ℝ) × IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ =>
      (‖Φ (AdelicEpstein.point p.1.2 p.2 p.1.1 ξ)‖₊ : ℝ≥0∞) :=
  measurable_ennnorm_comp_point_generic measurable_coe_archIdele hΦ ξ

private theorem orbitFn_globalPointsGL_rowRep_smul (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ automorphicSubmodule ω a b Φ₀)
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ t : ℝ) (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (v : {v : Fin 3 → ℚ // v ≠ 0}) :
    orbitFn F Φ σ t u (globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v) • g) =
      (‖F g‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) *
        (ENNReal.ofReal (t ^ (3 * σ)) * (‖Φ (AdelicEpstein.point t u g v.1)‖₊ : ℝ≥0∞)) := by
  unfold orbitFn
  rw [smul_eq_mul, ((mem_automorphicSubmodule_iff ω a b Φ₀ F).1 hF).1 (rowRep v) g, ideleNorm_det_globalPointsGL_mul,
    point_eq_row_two_centralScalarGL_mul_rowRep_mul]
  rfl

private theorem lintegral_nnnorm_sq_mul_epsteinPlus_eq (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (du : MeasureTheory.Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)) [IsFiniteMeasure du]
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (hΦ : Measurable Φ) (σ : ℝ) :
    ∫⁻ g, (‖F g‖₊ : ℝ≥0∞) ^ 2 * AdelicEpstein.epsteinPlus du Φ σ g ∂(domainMeasure a b Φ₀) =
      ∫⁻ t, ∫⁻ u, ∫⁻ g in Φ₀, ∑' v : {v : Fin 3 → ℚ // v ≠ 0},
        orbitFn F Φ σ t u
          (globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v) • g) ∂(slabMeasure a b) ∂du ∂AdelicEpstein.scaleMeasure := by
  have hFc := (mem_cuspFunctions_iff ω a b Φ₀ F).1 hF
  haveI : SFinite AdelicEpstein.scaleMeasure := by
    unfold AdelicEpstein.scaleMeasure
    infer_instance
  haveI : SFinite (slabMeasure a b) := by
    unfold slabMeasure
    infer_instance

  have hpt : ∀ (t : ℝ) (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      (∑' v : {v : Fin 3 → ℚ // v ≠ 0}, orbitFn F Φ σ t u (globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v) • g)) =
        (‖F g‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) *
          (ENNReal.ofReal (t ^ (3 * σ)) *
            ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (AdelicEpstein.point t u g ξ.1)‖₊ : ℝ≥0∞)) := by
    intro t u g
    simp only [orbitFn_globalPointsGL_rowRep_smul ω a b Φ₀ hFc.1, ENNReal.tsum_mul_left]
  simp only [hpt]

  have hAtop : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (‖F g‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) ≠ ⊤ := fun g =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) ENNReal.ofReal_ne_top
  have hL : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (‖F g‖₊ : ℝ≥0∞) ^ 2 * AdelicEpstein.epsteinPlus du Φ σ g =
      ∫⁻ t, ∫⁻ u, (‖F g‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) *
        (ENNReal.ofReal (t ^ (3 * σ)) *
          ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (AdelicEpstein.point t u g ξ.1)‖₊ : ℝ≥0∞)) ∂du
        ∂AdelicEpstein.scaleMeasure := by
    intro g
    unfold AdelicEpstein.epsteinPlus
    rw [← mul_assoc, ← lintegral_const_mul' _ _ (hAtop g)]
    refine lintegral_congr fun t => ?_
    rw [lintegral_const_mul' _ _ (hAtop g), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

  have hA : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      (‖F g‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) :=
    (measurable_nnnorm_sq hFc.2.1).mul (measurable_ofReal_ideleNorm_det_rpow σ)
  have hW : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (3 * σ)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const (3 * σ))
  have hJ : Measurable fun p : (AdelicGL 3 (𝓞 ℚ) ℚ × ℝ) × IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ =>
      (‖F p.1.1‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det p.1.1) ^ σ) *
        (ENNReal.ofReal (p.1.2 ^ (3 * σ)) *
          ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (AdelicEpstein.point p.1.2 p.2 p.1.1 ξ.1)‖₊ : ℝ≥0∞)) :=
    (hA.comp (measurable_fst.comp measurable_fst)).mul ((hW.comp (measurable_snd.comp measurable_fst)).mul
      (Measurable.tsum fun ξ => measurable_ennnorm_comp_point hΦ ξ.1))

  have hswap₁ : AEMeasurable (Function.uncurry fun (g : AdelicGL 3 (𝓞 ℚ) ℚ) (t : ℝ) =>
      ∫⁻ u, (‖F g‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) *
        (ENNReal.ofReal (t ^ (3 * σ)) *
          ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (AdelicEpstein.point t u g ξ.1)‖₊ : ℝ≥0∞)) ∂du)
      (((slabMeasure a b).restrict Φ₀).prod AdelicEpstein.scaleMeasure) :=
    (hJ.lintegral_prod_right' (ν := du)).aemeasurable

  have hswap₂ : ∀ t : ℝ, AEMeasurable (Function.uncurry fun (g : AdelicGL 3 (𝓞 ℚ) ℚ)
      (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) =>
        (‖F g‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) *
          (ENNReal.ofReal (t ^ (3 * σ)) *
            ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (AdelicEpstein.point t u g ξ.1)‖₊ : ℝ≥0∞)))
      (((slabMeasure a b).restrict Φ₀).prod du) := fun t =>
    (hJ.comp (show Measurable fun q : AdelicGL 3 (𝓞 ℚ) ℚ × IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ =>
      ((q.1, t), q.2) from (measurable_fst.prodMk measurable_const).prodMk measurable_snd)).aemeasurable
  rw [domainMeasure_def, lintegral_congr hL, lintegral_lintegral_swap hswap₁]
  exact lintegral_congr fun t => lintegral_lintegral_swap (hswap₂ t)

end MirabolicUnfolding
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isFundamentalDomain_mirabolic_and_lintegral_domainMeasure_eq_mul_lintegral.MirabolicUnfolding"

open MirabolicUnfolding in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (du : MeasureTheory.Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ))
    [MeasureTheory.IsFiniteMeasure du] [NeZero du] :
    let P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ) :=
      Subgroup.closure {g | (fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) = Pi.single 2 1} ⊓
        (globalPointsGL 3 (𝓞 ℚ) ℚ).range
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      ∃ Ω : Set (AdelicGL 3 (𝓞 ℚ) ℚ),
        MeasureTheory.IsFundamentalDomain P Ω (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ∧
      ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, F ∈ cuspFunctions ω a b Φ₀ →
        ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, Measurable Φ →
          ∀ σ : ℝ,
            ∫⁻ g, (‖F g‖₊ : ℝ≥0∞) ^ 2 * AdelicEpstein.epsteinPlus du Φ σ g ∂(domainMeasure a b Φ₀) =
              c * ∫⁻ g in Ω,
                    (‖F g‖₊ : ℝ≥0∞) ^ 2 *
                      (‖Φ (fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j)‖₊ : ℝ≥0∞) *
                      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ)
                  ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  intro P
  have ha : 0 < a := hΦ₀.1
  have hab : a < b := hΦ₀.2.1

  obtain ⟨Ω, hΩ⟩ := exists_isFundamentalDomain_mirabolic_of_isSlabDomain a b Φ₀ hΦ₀ P inf_le_right _
    (isFundamentalDomain_mirabolic_iUnion a b Φ₀ hΦ₀)
  have hlog : 0 < Real.log (b / a) / 3 := div_pos (Real.log_pos ((one_lt_div ha).2 hab)) (by norm_num)
  refine ⟨du Set.univ * ENNReal.ofReal (Real.log (b / a) / 3), ?_, ?_, Ω, hΩ, ?_⟩
  · exact ENNReal.mul_pos (MeasureTheory.Measure.measure_univ_ne_zero.2 (NeZero.ne du)) (ENNReal.ofReal_pos.2 hlog).ne'
  · exact ENNReal.mul_lt_top (MeasureTheory.measure_lt_top du _) ENNReal.ofReal_lt_top
  · intro F hF Φ hΦ σ
    have hFc := (mem_cuspFunctions_iff ω a b Φ₀ F).1 hF
    have hFinv : ∀ p ∈ mirabolic, ∀ g, ‖F (p * g)‖₊ = ‖F g‖₊ := by
      intro p hp g
      obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 (mirabolic_le_range hp)
      rw [← hγ, ((mem_automorphicSubmodule_iff ω a b Φ₀ F).1 hFc.1).1 γ g]

    change _ = _ * ∫⁻ g in Ω, rhsIntegrand F Φ σ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)

    rw [lintegral_nnnorm_sq_mul_epsteinPlus_eq ω a b Φ₀ du F hF Φ hΦ σ]

    have hT : ∀ t : ℝ, 0 < t →
        (∫⁻ u, ∫⁻ g in Φ₀, ∑' v : {v : Fin 3 → ℚ // v ≠ 0},
            orbitFn F Φ σ t u (globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v) • g) ∂(slabMeasure a b) ∂du) =
          du Set.univ * ∫⁻ h in Ω, (slice a b t).indicator (rhsIntegrand F Φ σ) h
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
      intro t ht
      have hu : ∀ u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ,
          ∫⁻ g in Φ₀, ∑' v : {v : Fin 3 → ℚ // v ≠ 0},
              orbitFn F Φ σ t u (globalPointsGL 3 (𝓞 ℚ) ℚ (rowRep v) • g) ∂(slabMeasure a b) =
            ∫⁻ h in Ω, (slice a b t).indicator (rhsIntegrand F Φ σ) h
              ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := fun u => by
        rw [setLIntegral_tsum_smul_eq a b Φ₀ hΦ₀ (measurable_orbitFn hFc.2.1 hΦ σ t u),
          setLIntegral_orbitFn_eq_setLIntegral_indicator_slice ω hω a b Φ₀ hFc.1 hFinv Φ σ
            (isFundamentalDomain_mirabolic_iUnion a b Φ₀ hΦ₀) hΩ ht u]
      rw [MeasureTheory.lintegral_congr hu, MeasureTheory.lintegral_const, mul_comm]

    rw [lintegral_scaleMeasure_congr _ _ hT,
      MeasureTheory.lintegral_const_mul' _ _ (MeasureTheory.measure_ne_top du _),
      lintegral_scaleMeasure_setLIntegral_indicator_slice a b ha hab Ω _ (measurable_rhsIntegrand hFc.2.1 hΦ σ)
        (rhsIntegrand_ne_top F Φ σ),
      mul_assoc]

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isFundamentalDomain_mirabolic_and_lintegral_domainMeasure_eq_mul_lintegral.MirabolicUnfolding"

end S_LanglandsTunnell_CubicInduction_exists_isFundamentalDomain_mirabolic_and_lintegral_domainMeasure_eq_mul_lintegral
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isFundamentalDomain_mirabolic_and_lintegral_domainMeasure_eq_mul_lintegral (solution)
