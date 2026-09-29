-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_pos_forall_integral_haar_eq_mul_integral_pi_det_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3f038615-2790-5a52-93d3-5604dc564317

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_map_bigCell_withDensity_eq_pi_withDensity_det_inv_sq
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_haar_eq_mul_integral_pi_det_inv_sq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
open scoped ENNReal NNReal Classical

noncomputable section

namespace E3ReduceSupplyF

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ

theorem level_zero :
    (∀ x : Qp, Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ p x = 1) ∧
      ∃ x : Qp, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : Qp, Valued.v x ≤ WithZero.exp k → NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
    (NumberField.StandardAddChar.psiLocal ℚ p) hk (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

theorem level_zero_inv :
    (∀ x : Qp, Valued.v x ≤ WithZero.exp (0 : ℤ) → (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x = 1) ∧
      ∃ x : Qp, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x ≠ 1 := by
  obtain ⟨h0, h1⟩ := level_zero p
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [AddChar.inv_apply]; exact h0 (-x) (by rwa [Valuation.map_neg])
  · obtain ⟨x, hx, hne⟩ := h1
    refine ⟨-x, by rwa [Valuation.map_neg], ?_⟩
    rwa [AddChar.inv_apply, neg_neg]

theorem selfDualHaarAt_eq :
    selfDualHaarAt ℚ p = @Measure.addHaarMeasure (p.adicCompletion ℚ) _ _ _ (localBorel ℚ p)
      (borelSpace_localBorel ℚ p) (integersPositiveCompacts ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p]
  simp

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  rw [selfDualHaarAt_eq p]
  infer_instance

theorem isSchwartzBruhat_tateFourier_psiLocal_inv (φ : Qp → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ p
    IsSchwartzBruhat (tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨h0, h1⟩ := level_zero_inv p
  exact LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier ℚ p (selfDualHaarAt ℚ p)
    ((NumberField.StandardAddChar.psiLocal ℚ p)⁻¹) 0 h0 h1 φ hφ

theorem continuous_tateFourier_of_isSchwartzBruhat (φ : Qp → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ p
    Continuous (tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ) :=
  (isSchwartzBruhat_tateFourier_psiLocal_inv p φ hφ).1.continuous

end E3ReduceSupplyF

namespace E3cH

variable (p : HeightOneSpectrum (𝓞 ℚ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_units : SecondCountableTopology (p.adicCompletion ℚ)ˣ :=
  (Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).secondCountableTopology

theorem borelSpace_units [MeasurableSpace (p.adicCompletion ℚ)] [BorelSpace (p.adicCompletion ℚ)] :
    BorelSpace (p.adicCompletion ℚ)ˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := p.adicCompletion ℚ)]
    rfl⟩

private theorem _root_.E3cH.isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

p2m_export "E3cH" "isAddHaarMeasure_selfDualHaarAt"
end E3cH
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_haar_eq_mul_integral_pi_det_inv_sq.E3cH"

namespace HLGlue

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem isEmbedding_coe : Topology.IsEmbedding (Units.val : G2 → Mat) := by
  refine Units.isEmbedding_val_mk' (f := fun X : Mat => X⁻¹) ?_ (fun u => (Matrix.coe_units_inv u).symm)
  intro X hX
  refine (continuousAt_matrix_inv X ?_).continuousWithinAt
  have hdet : X.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det X).1 hX
    exact this.ne_zero
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hdet

theorem range_coe : Set.range (Units.val : G2 → Mat) = {X : Mat | X.det ≠ 0} := by
  ext X
  constructor
  · rintro ⟨u, rfl⟩
    exact (Matrix.isUnits_det_units u).ne_zero
  · intro hX
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X hX, rfl⟩

theorem continuous_det' : Continuous fun X : Mat => X.det :=
  continuous_id.matrix_det

theorem isOpen_det_ne_zero : IsOpen {X : Mat | X.det ≠ 0} :=
  isOpen_ne.preimage (continuous_det' p)

theorem continuous_unipotentGL2 : Continuous fun x : F => (unipotentGL2 x : G2) := by
  have hval : Continuous fun x : F => ((unipotentGL2 x : G2) : Mat) := by
    refine continuous_matrix ?_
    intro i j
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have : (fun x : F => (((unipotentGL2 x : G2)⁻¹ : G2) : Mat)) = (fun x : F => ((unipotentGL2 x : G2) : Mat)) ∘ (fun x : F => -x) := by
    funext x
    simp only [Function.comp_apply]
    have h : (unipotentGL2 (-x) : G2) = (unipotentGL2 x)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
    rw [← h]
  rw [this]
  exact hval.comp continuous_neg

theorem continuous_lowerUnipotentGL2 : Continuous fun x : F => (lowerUnipotentGL2 x : G2) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix ?_
    intro i j
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotentGL2_coe] <;> fun_prop
  · have : (fun x : F => (((lowerUnipotentGL2 x : G2)⁻¹ : G2) : Mat)) = fun x : F => (!![1, 0; -x, 1] : Mat) := by
      funext x; rfl
    rw [this]
    refine continuous_matrix ?_
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_diagUnits2 : Continuous fun q : (F)ˣ × (F)ˣ => (diagUnits2 q.1 q.2 : G2) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun q : (F)ˣ × (F)ˣ => ((diagUnits2 q.1 q.2 : G2) : Mat)
    have : (fun q : (F)ˣ × (F)ˣ => ((diagUnits2 q.1 q.2 : G2) : Mat)) = fun q => !![(q.1 : F), 0; 0, (q.2 : F)] := by
      funext q; rfl
    rw [this]
    refine continuous_matrix ?_
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons,
        Matrix.head_fin_const]
    · exact Units.continuous_val.comp continuous_fst
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_val.comp continuous_snd
  · show Continuous fun q : (F)ˣ × (F)ˣ => (((diagUnits2 q.1 q.2 : G2)⁻¹ : G2) : Mat)
    have : (fun q : (F)ˣ × (F)ˣ => (((diagUnits2 q.1 q.2 : G2)⁻¹ : G2) : Mat)) =
        fun q => !![((q.1⁻¹ : (F)ˣ) : F), 0; 0, ((q.2⁻¹ : (F)ˣ) : F)] := by
      funext q; rfl
    rw [this]
    refine continuous_matrix ?_
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons,
        Matrix.head_fin_const]
    · exact Units.continuous_coe_inv.comp continuous_fst
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_coe_inv.comp continuous_snd

theorem continuous_cell : Continuous fun q : F × (F)ˣ × (F)ˣ × F =>
    (lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1 : G2) := by
  refine ((?_ : Continuous fun q : F × (F)ˣ × (F)ˣ × F => (lowerUnipotentGL2 q.2.2.2 : G2)).mul ?_).mul ?_
  · exact (continuous_lowerUnipotentGL2 p).comp (by fun_prop)
  · exact (continuous_diagUnits2 p).comp ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk (continuous_fst.comp continuous_snd))
  · exact (continuous_unipotentGL2 p).comp continuous_fst

end HLGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_haar_eq_mul_integral_pi_det_inv_sq.E3cH"

open HLGlue in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∃ κ : ℝ, 0 < κ ∧
        ∀ (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ), Integrable f μ₂ →
          Integrable (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
              if h : X.det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero X h) * ((((modulus X.det : ℝ) : ℂ)) ^ 2)⁻¹ else 0)
            (MeasureTheory.Measure.pi fun _ : Fin 2 => MeasureTheory.Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) ∧
          ∫ g, f g ∂μ₂ =
            (κ : ℂ) * ∫ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
              (if h : X.det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero X h) * ((((modulus X.det : ℝ) : ℂ)) ^ 2)⁻¹ else 0)
              ∂(MeasureTheory.Measure.pi fun _ : Fin 2 => MeasureTheory.Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI iGL : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI iBGL : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _
  classical
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := E3cH.borelSpace_units p
  haveI : SecondCountableTopology (p.adicCompletion ℚ)ˣ := E3cH.secondCountableTopology_units p
  letI iM : MeasurableSpace (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := MeasurableSpace.pi
  haveI iBM : BorelSpace (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → p.adicCompletion ℚ))
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  haveI hτ : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure :=
    LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

  obtain ⟨c, hc0, hctop, hμ⟩ :=
    AutomorphicForm.exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2 ℚ p μ₂
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
  have hB := LanglandsTunnell.RankinSelberg.map_bigCell_withDensity_eq_pi_withDensity_det_inv_sq p

  have hME : MeasurableEmbedding (Units.val : GL (Fin 2) (p.adicCompletion ℚ) → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := by
    refine (isEmbedding_coe p).measurableEmbedding ?_
    rw [range_coe]
    exact (isOpen_det_ne_zero p).measurableSet
  have hcellm : Measurable fun q : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
      (lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1 : GL (Fin 2) (p.adicCompletion ℚ)) :=
    (continuous_cell p).measurable

  set D : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℝ≥0 := fun X =>
    {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | X.det ≠ 0}.indicator (fun X => ((modulus X.det) ^ 2)⁻¹) X with hD
  have hmodc : Continuous fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => modulus X.det := by
    have h := LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm (K := ℚ) (v := p)
    have : (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => modulus X.det) = fun X => ‖X.det‖₊ := by
      funext X; rw [h]
    rw [this]
    exact continuous_nnnorm.comp (continuous_det' p)
  have hDm : Measurable D := by
    rw [hD]
    exact ((hmodc.measurable.pow_const 2).inv).indicator (isOpen_det_ne_zero p).measurableSet
  have hDeq : (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
      {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | X.det ≠ 0}.indicator
        (fun X => (((modulus X.det : ℝ≥0∞)) ^ 2)⁻¹) X) = fun X => (D X : ℝ≥0∞) := by
    funext X
    simp only [hD]
    by_cases hX : X ∈ {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | X.det ≠ 0}
    · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX]
      have hm : modulus X.det ≠ 0 := by
        rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; exact nnnorm_ne_zero_iff.2 hX
      rw [ENNReal.coe_inv (pow_ne_zero _ hm), ENNReal.coe_pow]
    · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hX, ENNReal.coe_zero]
  set ν' : Measure (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
    (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p).withDensity fun X => (D X : ℝ≥0∞) with hν'
  have hmap : Measure.map (Units.val : GL (Fin 2) (p.adicCompletion ℚ) → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) μ₂ = c • ν' := by
    rw [hμ, Measure.map_smul, Measure.map_map hME.measurable hcellm, hν']
    congr 1
    exact hB.trans (congrArg _ hDeq)
  have hcR : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  refine ⟨c.toReal, hcR, fun f hf => ?_⟩

  set G : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ := fun X =>
    if h : X.det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero X h) else 0 with hG
  have hGf : G ∘ (Units.val : GL (Fin 2) (p.adicCompletion ℚ) → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = f := by
    funext g
    simp only [Function.comp_apply, hG]
    rw [dif_pos (Matrix.isUnits_det_units g).ne_zero]
    congr 1
    exact Units.ext rfl
  have hFG : (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
      if h : X.det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero X h) * ((((modulus X.det : ℝ) : ℂ)) ^ 2)⁻¹ else 0) =
      fun X => D X • G X := by
    funext X
    simp only [hD, hG]
    by_cases hX : X.det ≠ 0
    · have h2 : X ∈ {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | X.det ≠ 0} := hX
      rw [dif_pos hX, dif_pos hX, Set.indicator_of_mem h2, NNReal.smul_def, Complex.real_smul]
      push_cast
      ring
    · rw [dif_neg hX, dif_neg hX, smul_zero]

  have hGint : Integrable G (Measure.map (Units.val : GL (Fin 2) (p.adicCompletion ℚ) → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) μ₂) := by
    rw [hME.integrable_map_iff, hGf]; exact hf
  have hGint' : Integrable G ν' := by
    rw [hmap] at hGint
    have := hGint.smul_measure (ENNReal.inv_ne_top.2 hc0)
    rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul] at this
  refine ⟨?_, ?_⟩
  · rw [hFG]
    rw [hν'] at hGint'
    exact (integrable_withDensity_iff_integrable_smul hDm).1 hGint'
  · rw [hFG]
    calc ∫ g, f g ∂μ₂
        = ∫ X, G X ∂(Measure.map (Units.val : GL (Fin 2) (p.adicCompletion ℚ) → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) μ₂) := by
          rw [hME.integral_map]
          change ∫ g, f g ∂μ₂ = ∫ x, (G ∘ Units.val) x ∂μ₂
          rw [hGf]
      _ = ∫ X, G X ∂(c • ν') := by rw [hmap]
      _ = (c.toReal : ℂ) * ∫ X, G X ∂ν' := by rw [integral_smul_measure, Complex.real_smul]
      _ = (c.toReal : ℂ) * ∫ X, D X • G X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by
          rw [hν']
          congr 1
          exact integral_withDensity_eq_integral_smul hDm _

end
end S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_haar_eq_mul_integral_pi_det_inv_sq
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_haar_eq_mul_integral_pi_det_inv_sq (solution)
