-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integral_matFourier22_lowerTriangular_eq_integral_integral_upperTriangular_mul_psiLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/48b5a308-7717-55a7-9298-85b9f5d32838

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_selfDualHaarAt_of_isSchwartzBruhat
import Theorems.Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_matFourier22_lowerTriangular_eq_integral_integral_upperTriangular_mul_psiLocal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

noncomputable section

namespace GJFS

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "M2" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
local notation "ψ" => (NumberField.StandardAddChar.psiLocal ℚ p)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  unfold selfDualHaarAt
  refine Measure.IsAddHaarMeasure.nnreal_smul _ ?_
  have hq : (0 : NNReal) < (Ideal.absNorm p.asIdeal : NNReal) :=
    zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p)
  exact (NNReal.rpow_pos hq).ne'

theorem sb_partial {A B : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [MeasurableSpace B] (ν : Measure B)
    (Φ : A × B → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) (k : B → ℂ) :
    IsLocallyConstant (fun a => ∫ b, Φ (a, b) * k b ∂ν) ∧ HasCompactSupport (fun a => ∫ b, Φ (a, b) * k b ∂ν) := by
  obtain ⟨W, hWo, hW1, hW⟩ := IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
      (G := Multiplicative (A × B)) (fun x => Φ (Multiplicative.toAdd x)) hΦ.1 hΦ.2
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro a₀
    have hc : Continuous fun a : A => Multiplicative.ofAdd ((a - a₀, (0 : B))) :=
      continuous_ofAdd.comp ((continuous_id.sub continuous_const).prodMk continuous_const)
    have hV : {a : A | Multiplicative.ofAdd ((a - a₀, (0 : B))) ∈ W} ∈ nhds a₀ := by
      refine (hWo.preimage hc).mem_nhds ?_
      show Multiplicative.ofAdd ((a₀ - a₀, (0 : B))) ∈ W
      rw [sub_self]; exact hW1
    filter_upwards [hV] with a ha
    congr 1
    funext b
    congr 1
    have := (hW (Multiplicative.ofAdd (a₀, b)) _ ha).1
    simp only [← ofAdd_add, toAdd_ofAdd, Prod.mk_add_mk, add_zero] at this
    rw [← this]
    congr 2
    abel
  · refine HasCompactSupport.intro (hΦ.2.image continuous_fst) fun a ha => ?_
    have h0 : ∀ b, Φ (a, b) = 0 := fun b =>
      image_eq_zero_of_notMem_tsupport (fun h => ha ⟨(a, b), h, rfl⟩)
    simp [h0]

def ofCols (w c : F × F) : M2 := !![w.1, c.1; w.2, c.2]

theorem continuous_ofCols : Continuous fun z : (F × F) × (F × F) => ofCols p z.1 z.2 := by
  unfold ofCols
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_fst.comp continuous_fst
  · exact continuous_fst.comp continuous_snd
  · exact continuous_snd.comp continuous_fst
  · exact continuous_snd.comp continuous_snd

def Ψcol (Ψ : M2 → ℂ) (z : (F × F) × (F × F)) : ℂ := Ψ (ofCols p z.1 z.2)

theorem sb_Ψcol (Ψ : M2 → ℂ) (hΨ : IsSchwartzBruhat Ψ) :
    IsLocallyConstant (Ψcol p Ψ) ∧ HasCompactSupport (Ψcol p Ψ) := by
  refine ⟨hΨ.1.comp_continuous (continuous_ofCols p), ?_⟩

  set D : Fin 2 → Fin 2 → Set F := fun i j => (fun X : M2 => X i j) '' tsupport Ψ with hD
  have hDc : ∀ i j, IsCompact (D i j) := fun i j => hΨ.2.image (continuous_apply_apply i j)
  refine HasCompactSupport.intro (((hDc 0 0).prod (hDc 1 0)).prod ((hDc 0 1).prod (hDc 1 1))) fun z hz => ?_
  unfold Ψcol
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  apply hz
  simp only [Set.mem_prod, hD]
  exact ⟨⟨⟨_, hmem, rfl⟩, ⟨_, hmem, rfl⟩⟩, ⟨⟨_, hmem, rfl⟩, ⟨_, hmem, rfl⟩⟩⟩

def fSlice (Ψ : M2 → ℂ) (δ : F) (w : F × F) : ℂ :=
  ∫ c : F × F, Ψcol p Ψ (w, c) * ψ (c.1 * 0 + c.2 * δ) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))

theorem sb_fSlice (Ψ : M2 → ℂ) (hΨ : IsSchwartzBruhat Ψ) (δ : F) :
    IsLocallyConstant (fSlice p Ψ δ) ∧ HasCompactSupport (fSlice p Ψ δ) :=
  sb_partial _ (Ψcol p Ψ) (sb_Ψcol p Ψ hΨ) _

def gSlice (Ψ : M2 → ℂ) (α δ : F) (w₂ : F) : ℂ :=
  ∫ w₁ : F, fSlice p Ψ δ (w₁, w₂) * ψ (w₁ * α) ∂(selfDualHaarAt ℚ p)

theorem sb_gSlice (Ψ : M2 → ℂ) (hΨ : IsSchwartzBruhat Ψ) (α δ : F) :
    IsSchwartzBruhat (gSlice p Ψ α δ) := by
  have hf := sb_fSlice p Ψ hΨ δ
  have hswap : IsLocallyConstant (fun z : F × F => fSlice p Ψ δ z.swap) ∧
      HasCompactSupport (fun z : F × F => fSlice p Ψ δ z.swap) :=
    ⟨hf.1.comp_continuous continuous_swap, hf.2.comp_homeomorph (Homeomorph.prodComm F F)⟩
  exact sb_partial _ (fun z : F × F => fSlice p Ψ δ z.swap) hswap (fun w₁ => ψ (w₁ * α))

theorem matFourier22_lower_eq (Ψ : M2 → ℂ) (α δ u : F) :
    matFourier22 p ψ Ψ !![α, 0; u, δ] =
      ∫ w : F × F, fSlice p Ψ δ w * ψ (w.1 * α + w.2 * u) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  rw [matFourier22_eq, colFourier22_apply]
  congr 1
  funext w
  have h00 : (!![α, 0; u, δ] : M2) 0 0 = α := rfl
  have h10 : (!![α, 0; u, δ] : M2) 1 0 = u := rfl
  rw [h00, h10]
  congr 1
  rw [colFourier22_apply]
  unfold fSlice Ψcol ofCols
  congr 1
  funext c
  have hM : setCol22 p (setCol22 p !![α, 0; u, δ] 0 w) 1 c = !![w.1, c.1; w.2, c.2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [setCol22_apply]
  have h01 : (setCol22 p !![α, 0; u, δ] 0 w) 0 1 = 0 := by simp [setCol22_apply]
  have h11 : (setCol22 p !![α, 0; u, δ] 0 w) 1 1 = δ := by simp [setCol22_apply]
  rw [hM, h01, h11]

theorem integral_fSlice_eq_tateFourier (Ψ : M2 → ℂ) (hΨ : IsSchwartzBruhat Ψ) (α δ u : F) :
    ∫ w : F × F, fSlice p Ψ δ w * ψ (w.1 * α + w.2 * u) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) =
      tateFourier ψ (selfDualHaarAt ℚ p) (gSlice p Ψ α δ) u := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  have hf := sb_fSlice p Ψ hΨ δ
  have hψc : Continuous ψ := NumberField.StandardAddChar.continuous_psiLocal ℚ p
  have hint : Integrable (fun w : F × F => fSlice p Ψ δ w * ψ (w.1 * α + w.2 * u))
      ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hf.2.mul_right
    exact hf.1.continuous.mul (hψc.comp ((continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)))
  rw [integral_prod_symm _ hint]
  unfold tateFourier gSlice
  congr 1
  funext w₂
  simp only []
  rw [← integral_mul_const]
  congr 1
  funext w₁
  rw [AddChar.map_add_eq_mul]
  ring

theorem integral_tateFourier_eq (Ψ : M2 → ℂ) (hΨ : IsSchwartzBruhat Ψ) (α δ : F) :
    ∫ u : F, tateFourier ψ (selfDualHaarAt ℚ p) (gSlice p Ψ α δ) u ∂(selfDualHaarAt ℚ p) = gSlice p Ψ α δ 0 := by
  have h := LanglandsTunnell.TateLocal.tateFourier_tateFourier_selfDualHaarAt_of_isSchwartzBruhat ℚ p
    (gSlice p Ψ α δ) (sb_gSlice p Ψ hΨ α δ) 0
  rw [neg_zero] at h
  rw [← h]
  show _ = ∫ x : F, tateFourier ψ (selfDualHaarAt ℚ p) (gSlice p Ψ α δ) x * ψ (x * 0) ∂(selfDualHaarAt ℚ p)
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]

theorem gSlice_zero_eq (Ψ : M2 → ℂ) (hΨ : IsSchwartzBruhat Ψ) (α δ : F) :
    gSlice p Ψ α δ 0 =
      ∫ vt : F × F, (∫ x : F, Ψ !![vt.1, x; 0, vt.2] ∂(selfDualHaarAt ℚ p)) * ψ (vt.1 * α + vt.2 * δ)
        ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  have hψc : Continuous ψ := NumberField.StandardAddChar.continuous_psiLocal ℚ p

  set K : F × (F × F) → ℂ := fun z => Ψ !![z.1, z.2.2; 0, z.2.1] * (ψ (z.2.2 * 0 + z.2.1 * δ) * ψ (z.1 * α)) with hK

  set D : Fin 2 → Fin 2 → Set F := fun i j => (fun X : M2 => X i j) '' tsupport Ψ with hD
  have hDc : ∀ i j, IsCompact (D i j) := fun i j => hΨ.2.image (continuous_apply_apply i j)
  have hKc : Continuous K := by
    have hm : Continuous fun z : F × (F × F) => (!![z.1, z.2.2; 0, z.2.1] : M2) := by
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_fst
      · exact continuous_snd.comp continuous_snd
      · exact continuous_const
      · exact continuous_fst.comp continuous_snd
    exact (hΨ.1.continuous.comp hm).mul
      ((hψc.comp (((continuous_snd.comp continuous_snd).mul continuous_const).add
        ((continuous_fst.comp continuous_snd).mul continuous_const))).mul (hψc.comp (continuous_fst.mul continuous_const)))
  have hKs : HasCompactSupport K := by
    refine HasCompactSupport.intro ((hDc 0 0).prod ((hDc 1 1).prod (hDc 0 1))) fun z hz => ?_
    have : Ψ !![z.1, z.2.2; 0, z.2.1] = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      apply hz
      simp only [Set.mem_prod, hD]
      exact ⟨⟨_, hmem, rfl⟩, ⟨_, hmem, rfl⟩, ⟨_, hmem, rfl⟩⟩
    simp [hK, this]
  have hKi : Integrable K ((selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) :=
    hKc.integrable_of_hasCompactSupport hKs

  have ha : gSlice p Ψ α δ 0 = ∫ z, K z ∂((selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) := by
    rw [integral_prod _ hKi]
    unfold gSlice
    congr 1
    funext w₁
    unfold fSlice Ψcol ofCols
    rw [← integral_mul_const, ← integral_prod_swap]
    congr 1
    funext z
    simp only [hK, Prod.fst_swap, Prod.snd_swap]
    ring

  have hb : ∫ z, K z ∂((selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) =
      ∫ z : (F × F) × F, K (MeasurableEquiv.prodAssoc z) ∂(((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)).prod (selfDualHaarAt ℚ p)) :=
    ((measurePreserving_prodAssoc (selfDualHaarAt ℚ p) (selfDualHaarAt ℚ p) (selfDualHaarAt ℚ p)).integral_comp' K).symm
  have hKi' : Integrable (fun z : (F × F) × F => K (MeasurableEquiv.prodAssoc z))
      (((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)).prod (selfDualHaarAt ℚ p)) :=
    (measurePreserving_prodAssoc (selfDualHaarAt ℚ p) (selfDualHaarAt ℚ p) (selfDualHaarAt ℚ p)).integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding |>.mpr hKi
  rw [ha, hb, integral_prod _ hKi']
  congr 1
  funext vt
  simp only [hK, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply]
  rw [← integral_mul_const]
  congr 1
  funext x
  rw [mul_zero, zero_add, AddChar.map_add_eq_mul]
  ring

theorem main (Ψ : M2 → ℂ) (hΨ : IsSchwartzBruhat Ψ) (α δ : F) :
    ∫ u : F, matFourier22 p ψ Ψ !![α, 0; u, δ] ∂(selfDualHaarAt ℚ p) =
      ∫ vt : F × F, (∫ x : F, Ψ !![vt.1, x; 0, vt.2] ∂(selfDualHaarAt ℚ p)) * ψ (vt.1 * α + vt.2 * δ)
        ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  have h1 : (fun u : F => matFourier22 p ψ Ψ !![α, 0; u, δ]) =
      fun u => tateFourier ψ (selfDualHaarAt ℚ p) (gSlice p Ψ α δ) u := by
    funext u
    rw [matFourier22_lower_eq, integral_fSlice_eq_tateFourier p Ψ hΨ]
  rw [h1, integral_tateFourier_eq p Ψ hΨ, gSlice_zero_eq p Ψ hΨ]

end GJFS

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Ψ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΨ : IsSchwartzBruhat Ψ)
    (α δ : p.adicCompletion ℚ) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∫ u : p.adicCompletion ℚ, matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Ψ !![α, 0; u, δ] ∂(selfDualHaarAt ℚ p) =
      ∫ vt : p.adicCompletion ℚ × p.adicCompletion ℚ,
        (∫ x : p.adicCompletion ℚ, Ψ !![vt.1, x; 0, vt.2] ∂(selfDualHaarAt ℚ p)) *
          NumberField.StandardAddChar.psiLocal ℚ p (vt.1 * α + vt.2 * δ)
        ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) :=
  GJFS.main p Ψ hΨ α δ

end S_LanglandsTunnell_CubicInduction_integral_matFourier22_lowerTriangular_eq_integral_integral_upperTriangular_mul_psiLocal
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integral_matFourier22_lowerTriangular_eq_integral_integral_upperTriangular_mul_psiLocal (solution)
