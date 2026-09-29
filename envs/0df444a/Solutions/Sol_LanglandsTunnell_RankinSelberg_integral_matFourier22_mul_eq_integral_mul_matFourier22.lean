-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.integral_matFourier22_mul_eq_integral_mul_matFourier22
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ed466f23-79ea-564e-a327-9f27b5368f79

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_integral_matFourier22_mul_eq_integral_mul_matFourier22
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
open scoped ENNReal NNReal

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

namespace GJJLParseval

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

def shuffle : (α × α) × (α × α) ≃ᵐ (α × α) × (α × α) :=
  (MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl α).prodCongr
      ((MeasurableEquiv.prodAssoc.symm.trans (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl α))).trans
        MeasurableEquiv.prodAssoc))).trans
  MeasurableEquiv.prodAssoc.symm

theorem shuffle_apply (x : (α × α) × (α × α)) : shuffle x = ((x.1.1, x.2.1), (x.1.2, x.2.2)) := rfl

theorem measurePreserving_shuffle (μ : Measure α) [SFinite μ] :
    MeasurePreserving (shuffle (α := α)) ((μ.prod μ).prod (μ.prod μ)) ((μ.prod μ).prod (μ.prod μ)) := by
  have h1 := measurePreserving_prodAssoc μ μ (μ.prod μ)
  have h2 : MeasurePreserving (fun x : α × ((α × α) × α) => (x.1, ((x.2.1.2, x.2.1.1), x.2.2)))
      (μ.prod ((μ.prod μ).prod μ)) (μ.prod ((μ.prod μ).prod μ)) :=
    (MeasurePreserving.id μ).prod ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).prod (MeasurePreserving.id μ))
  have h3 := measurePreserving_prodAssoc μ μ μ
  have h3' := h3.symm MeasurableEquiv.prodAssoc
  have h4 : MeasurePreserving (fun x : α × (α × (α × α)) => (x.1, ((x.2.1, x.2.2.1), x.2.2.2)))
      (μ.prod (μ.prod (μ.prod μ))) (μ.prod ((μ.prod μ).prod μ)) := (MeasurePreserving.id μ).prod h3'
  have h5 : MeasurePreserving (fun x : α × ((α × α) × α) => (x.1, (x.2.1.1, (x.2.1.2, x.2.2))))
      (μ.prod ((μ.prod μ).prod μ)) (μ.prod (μ.prod (μ.prod μ))) := (MeasurePreserving.id μ).prod h3
  have h6 := (measurePreserving_prodAssoc μ μ (μ.prod μ)).symm MeasurableEquiv.prodAssoc
  have : (shuffle (α := α) : (α × α) × (α × α) → (α × α) × (α × α)) =
      (MeasurableEquiv.prodAssoc.symm : α × (α × (α × α)) → (α × α) × (α × α)) ∘
        (fun x : α × ((α × α) × α) => (x.1, (x.2.1.1, (x.2.1.2, x.2.2)))) ∘
        (fun x : α × ((α × α) × α) => (x.1, ((x.2.1.2, x.2.1.1), x.2.2))) ∘
        (fun x : α × (α × (α × α)) => (x.1, ((x.2.1, x.2.2.1), x.2.2.2))) ∘
        (MeasurableEquiv.prodAssoc : (α × α) × (α × α) → α × (α × (α × α))) := by
    funext x; rfl
  rw [this]
  exact h6.comp (h5.comp (h2.comp (h4.comp h1)))

def rowEquiv : (Fin 2 → Fin 2 → α) ≃ᵐ (α × α) × (α × α) :=
  (MeasurableEquiv.finTwoArrow (α := Fin 2 → α)).trans
    (MeasurableEquiv.finTwoArrow.prodCongr MeasurableEquiv.finTwoArrow)

theorem rowEquiv_apply (X : Fin 2 → Fin 2 → α) : rowEquiv X = ((X 0 0, X 0 1), (X 1 0, X 1 1)) := rfl

theorem measurePreserving_rowEquiv (μ : Measure α) [SigmaFinite μ] :
    MeasurePreserving (rowEquiv : (Fin 2 → Fin 2 → α) → (α × α) × (α × α))
      (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) ((μ.prod μ).prod (μ.prod μ)) := by
  have : (rowEquiv : (Fin 2 → Fin 2 → α) → (α × α) × (α × α)) =
      (fun z : (Fin 2 → α) × (Fin 2 → α) => (MeasurableEquiv.finTwoArrow z.1, MeasurableEquiv.finTwoArrow z.2)) ∘
        (MeasurableEquiv.finTwoArrow : (Fin 2 → Fin 2 → α) → (Fin 2 → α) × (Fin 2 → α)) := by
    funext X; rfl
  rw [this]
  exact ((measurePreserving_finTwoArrow μ).prod (measurePreserving_finTwoArrow μ)).comp
    (measurePreserving_finTwoArrow (Measure.pi fun _ : Fin 2 => μ))

def colEquiv : (Fin 2 → Fin 2 → α) ≃ᵐ (α × α) × (α × α) := rowEquiv.trans shuffle

theorem colEquiv_apply (X : Fin 2 → Fin 2 → α) : colEquiv X = ((X 0 0, X 1 0), (X 0 1, X 1 1)) := rfl

theorem measurePreserving_colEquiv (μ : Measure α) [SigmaFinite μ] :
    MeasurePreserving (colEquiv : (Fin 2 → Fin 2 → α) → (α × α) × (α × α))
      (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) ((μ.prod μ).prod (μ.prod μ)) := by
  have : (colEquiv : (Fin 2 → Fin 2 → α) → (α × α) × (α × α)) = shuffle ∘ rowEquiv := rfl
  rw [this]
  exact (measurePreserving_shuffle μ).comp (measurePreserving_rowEquiv μ)

end GJJLParseval

namespace GJJLParseval

open NumberField.StandardAddChar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

theorem isLocallyConstant_psiLocal : IsLocallyConstant (fun t : F => (psiLocal ℚ p t : ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen ((fun y : F => y - x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F)) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_id.sub continuous_const)
  have hmem : x ∈ (fun y : F => y - x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F) := by
    simp only [Set.mem_preimage, sub_self, SetLike.mem_coe]; exact zero_mem _
  filter_upwards [hopen.mem_nhds hmem] with y hy
  have h1 : psiLocal ℚ p (y - x) = 1 := by
    apply (E3ReduceSupplyF.level_zero p).1
    rw [WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hy
  have : y = (y - x) + x := by ring
  rw [this, AddChar.map_add_eq_mul, h1, one_mul]

theorem continuous_psiLocal : Continuous (fun t : F => (psiLocal ℚ p t : ℂ)) :=
  (isLocallyConstant_psiLocal p).continuous

theorem setCol22_setCol22_colEquiv (X Y : Matrix (Fin 2) (Fin 2) F) :
    setCol22 p (setCol22 p X 0 (Y 0 0, Y 1 0)) 1 (Y 0 1, Y 1 1) = Y := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [setCol22_apply]

end GJJLParseval

open GJJLParseval in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (Φ Ψ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ → IsLocallyConstant Ψ → HasCompactSupport Ψ →
      ∫ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ), matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ X * Ψ X ∂(MeasureTheory.Measure.pi fun _ : Fin 2 => MeasureTheory.Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) =
        ∫ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ), Φ X * matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Ψ X ∂(MeasureTheory.Measure.pi fun _ : Fin 2 => MeasureTheory.Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  intro Φ Ψ hΦ hΦc hΨ hΨc
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  have hψc := continuous_psiLocal p
  set μ4 : Measure (Fin 2 → Fin 2 → p.adicCompletion ℚ) :=
    Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p with hμ4
  haveI hσ2 : SigmaFinite (Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := inferInstance
  haveI hc2 : IsFiniteMeasureOnCompacts (Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) :=
    Measure.pi.isFiniteMeasureOnCompacts _
  haveI hσ4 : SigmaFinite μ4 := by rw [hμ4]; infer_instance
  haveI hc4 : IsFiniteMeasureOnCompacts μ4 := by rw [hμ4]; exact Measure.pi.isFiniteMeasureOnCompacts _
  have hcolc : Continuous (colEquiv : (Fin 2 → Fin 2 → p.adicCompletion ℚ) →
      (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ)) := by
    have : (colEquiv : (Fin 2 → Fin 2 → p.adicCompletion ℚ) →
        (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ)) =
        fun Y => ((Y 0 0, Y 1 0), (Y 0 1, Y 1 1)) := funext fun Y => colEquiv_apply Y
    rw [this]
    fun_prop
  have hcolset : ∀ (X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
      (c : (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ)),
      (colEquiv : (Fin 2 → Fin 2 → p.adicCompletion ℚ) →
        (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ))
          (setCol22 p (setCol22 p X 0 c.1) 1 c.2) = c := by
    intro X c
    rw [colEquiv_apply]
    ext <;> simp [setCol22_apply]

  have hent : ∀ i j : Fin 2, Continuous fun X : Fin 2 → Fin 2 → p.adicCompletion ℚ => X i j := fun i j => by fun_prop

  have hFT : ∀ (φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant φ → HasCompactSupport φ →
      ∀ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
        matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) φ X =
          ∫ Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
            φ Y * NumberField.StandardAddChar.psiLocal ℚ p
              (Y 0 1 * X 0 1 + Y 1 1 * X 1 1 + (Y 0 0 * X 0 0 + Y 1 0 * X 1 0)) ∂μ4 := by
    intro φ hφ hφc X
    have hφcont : Continuous φ := hφ.continuous

    set Mx : (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ) →
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := fun c => setCol22 p (setCol22 p X 0 c.1) 1 c.2 with hMx
    have hMxc : Continuous Mx := by
      rw [hMx]
      refine continuous_pi fun i => continuous_pi fun k => ?_
      fin_cases i <;> fin_cases k <;> simp [setCol22_apply] <;> fun_prop
    set G : (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ) → ℂ := fun c =>
      φ (Mx c) * (NumberField.StandardAddChar.psiLocal ℚ p (c.2.1 * X 0 1 + c.2.2 * X 1 1) *
        NumberField.StandardAddChar.psiLocal ℚ p (c.1.1 * X 0 0 + c.1.2 * X 1 0)) with hG
    have hGc : Continuous G := by
      rw [hG]
      exact (hφcont.comp hMxc).mul ((hψc.comp (by fun_prop)).mul (hψc.comp (by fun_prop)))
    have hGsupp : HasCompactSupport G := by
      refine HasCompactSupport.intro' ((hφc.isCompact.image hcolc)) ((hφc.isCompact.image hcolc).isClosed) ?_
      intro c hc
      rw [hG]
      simp only
      have : φ (Mx c) = 0 := by
        by_contra hne
        apply hc
        refine ⟨Mx c, subset_tsupport _ (Function.mem_support.2 hne), ?_⟩
        rw [hMx]; exact hcolset X c
      rw [this, zero_mul]
    have hGint : Integrable G (((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) :=
      hGc.integrable_of_hasCompactSupport hGsupp

    rw [matFourier22_eq, colFourier22_apply]
    have hinner : ∀ u : p.adicCompletion ℚ × p.adicCompletion ℚ,
        colFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) 1 φ (setCol22 p X 0 u) *
            NumberField.StandardAddChar.psiLocal ℚ p (u.1 * X 0 0 + u.2 * X 1 0) =
          ∫ u' : p.adicCompletion ℚ × p.adicCompletion ℚ, G (u, u') ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
      intro u
      rw [colFourier22_apply, ← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
      rw [hG, hMx]
      simp only [setCol22_apply]
      simp
      ring
    simp_rw [hinner]
    rw [← integral_prod _ hGint, ← (measurePreserving_colEquiv (selfDualHaarAt ℚ p)).integral_comp' (f := colEquiv)]
    rw [hμ4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    rw [hG]
    simp only [colEquiv_apply]
    rw [hMx]
    simp only
    rw [setCol22_setCol22_colEquiv p X Y, ← AddChar.map_add_eq_mul]

  set H : (Fin 2 → Fin 2 → p.adicCompletion ℚ) × (Fin 2 → Fin 2 → p.adicCompletion ℚ) → ℂ := fun Z =>
    Φ Z.2 * NumberField.StandardAddChar.psiLocal ℚ p
      (Z.2 0 1 * Z.1 0 1 + Z.2 1 1 * Z.1 1 1 + (Z.2 0 0 * Z.1 0 0 + Z.2 1 0 * Z.1 1 0)) * Ψ Z.1 with hH
  have hHc : Continuous H := by
    rw [hH]
    exact ((hΦ.continuous.comp continuous_snd).mul (hψc.comp (by fun_prop))).mul (hΨ.continuous.comp continuous_fst)
  have hHsupp : HasCompactSupport H := by
    refine HasCompactSupport.intro' (hΨc.isCompact.prod hΦc.isCompact) ((isClosed_tsupport _).prod (isClosed_tsupport _)) ?_
    intro Z hZ
    have hZ' : Z.1 ∉ tsupport Ψ ∨ Z.2 ∉ tsupport Φ := by
      by_contra h
      push_neg at h
      exact hZ (Set.mk_mem_prod h.1 h.2)
    rw [hH]
    simp only
    rcases hZ' with h | h
    · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul, zero_mul]
  have hHint : Integrable H (μ4.prod μ4) := hHc.integrable_of_hasCompactSupport hHsupp

  have hL : (∫ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ X * Ψ X ∂μ4) = ∫ X, ∫ Y, H (X, Y) ∂μ4 ∂μ4 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    beta_reduce
    rw [hFT Φ hΦ hΦc X, hH]
    exact (integral_mul_const (Ψ X) _).symm
  have hR : (∫ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
      Φ X * matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Ψ X ∂μ4) = ∫ Y, ∫ X, H (X, Y) ∂μ4 ∂μ4 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    beta_reduce
    rw [hFT Ψ hΨ hΨc Y]
    symm
    calc (∫ X, H (X, Y) ∂μ4) = ∫ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ), Φ Y * (Ψ X *
          NumberField.StandardAddChar.psiLocal ℚ p (X 0 1 * Y 0 1 + X 1 1 * Y 1 1 + (X 0 0 * Y 0 0 + X 1 0 * Y 1 0))) ∂μ4 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
          beta_reduce
          rw [hH]
          simp only
          rw [show X 0 1 * Y 0 1 + X 1 1 * Y 1 1 + (X 0 0 * Y 0 0 + X 1 0 * Y 1 0) =
            Y 0 1 * X 0 1 + Y 1 1 * X 1 1 + (Y 0 0 * X 0 0 + Y 1 0 * X 1 0) by ring]
          ring
      _ = _ := integral_const_mul _ _
  rw [hL, hR]
  exact integral_integral_swap hHint

end
end S_LanglandsTunnell_RankinSelberg_integral_matFourier22_mul_eq_integral_mul_matFourier22
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_integral_matFourier22_mul_eq_integral_mul_matFourier22 (solution)
