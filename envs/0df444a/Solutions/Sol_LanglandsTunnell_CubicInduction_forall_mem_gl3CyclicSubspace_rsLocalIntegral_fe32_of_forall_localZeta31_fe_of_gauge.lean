-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d0831749-073b-5a62-9847-3b447ca71fef

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Theorems.Thm_LanglandsTunnell_CubicInduction_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit'"
p2m_attr_erase "instance" "RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply"
p2m_attr_erase "simp" "M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

open LanglandsTunnell.CubicInduction

noncomputable section

namespace P2primeTransport

section Cyc

variable {F : Type*} [CommRing F]

theorem mem_gl3CyclicSubspace_iff (W X : GL (Fin 3) F → ℂ) :
    X ∈ gl3CyclicSubspace W ↔ X ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 3) F => fun g => W (g * h)) :=
  Iff.rfl

theorem translate_mem {W X : GL (Fin 3) F → ℂ} (hX : X ∈ gl3CyclicSubspace W) (h : GL (Fin 3) F) :
    (fun g => X (g * h)) ∈ gl3CyclicSubspace W :=
  LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h hX

theorem self_translate_mem (W : GL (Fin 3) F → ℂ) (h : GL (Fin 3) F) :
    (fun g => W (g * h)) ∈ gl3CyclicSubspace W :=
  Submodule.subset_span ⟨h, rfl⟩

theorem self_mem (W : GL (Fin 3) F → ℂ) : W ∈ gl3CyclicSubspace W := by
  have := self_translate_mem W 1
  simpa using this

theorem cyc_le_of_mem {W X : GL (Fin 3) F → ℂ} (hX : X ∈ gl3CyclicSubspace W) :
    gl3CyclicSubspace X ≤ gl3CyclicSubspace W :=
  Submodule.span_le.mpr (by rintro _ ⟨h, rfl⟩; exact translate_mem hX h)

theorem law_of_mem {X₀ : Type*} (W : GL (Fin 3) F → ℂ) (n : X₀ → GL (Fin 3) F) (c : X₀ → ℂ)
    (hlaw : ∀ (x : X₀) (g : GL (Fin 3) F), W (n x * g) = c x * W g) :
    ∀ X ∈ gl3CyclicSubspace W, ∀ (x : X₀) (g : GL (Fin 3) F), X (n x * g) = c x * X g := by
  intro X hX
  induction hX using Submodule.span_induction with
  | mem W' hW' =>
    obtain ⟨h, rfl⟩ := hW'
    intro x g
    show W (n x * g * h) = c x * W (g * h)
    rw [mul_assoc, hlaw]
  | zero => intro x g; simp
  | add W₁ W₂ _ _ ih₁ ih₂ =>
    intro x g
    simp only [Pi.add_apply]
    rw [ih₁, ih₂, mul_add]
  | smul a W' _ ih =>
    intro x g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ih]
    ring

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem smooth_of_mem (W : GL (Fin 3) F → ℂ)
    (hsm : ∃ U : Subgroup (GL (Fin 3) F), IsOpen (U : Set (GL (Fin 3) F)) ∧ ∀ k ∈ U, ∀ g, W (g * k) = W g) :
    ∀ X ∈ gl3CyclicSubspace W,
      ∃ U : Subgroup (GL (Fin 3) F), IsOpen (U : Set (GL (Fin 3) F)) ∧ ∀ k ∈ U, ∀ g, X (g * k) = X g := by
  obtain ⟨K₀, hK₀, hfix⟩ := hsm
  intro X hX
  induction hX using Submodule.span_induction with
  | mem W' hW' =>
    obtain ⟨h, rfl⟩ := hW'
    refine ⟨K₀.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      refine hK₀.preimage ?_
      show Continuous fun k : GL (Fin 3) F => (MulAut.conj h⁻¹) k
      simp only [MulAut.conj_apply, inv_inv]
      fun_prop
    · intro k hk g
      rw [Subgroup.mem_comap] at hk
      have hk' : h⁻¹ * k * h ∈ K₀ := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hk
      show W (g * k * h) = W (g * h)
      calc W (g * k * h) = W (g * h * (h⁻¹ * k * h)) := by group
        _ = W (g * h) := hfix _ hk' _
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ ih₁ ih₂ =>
    obtain ⟨U₁, hU₁, h₁⟩ := ih₁
    obtain ⟨U₂, hU₂, h₂⟩ := ih₂
    refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => ?_⟩
    simp only [Pi.add_apply]
    rw [h₁ k hk.1 g, h₂ k hk.2 g]
  | smul a W' _ ih =>
    obtain ⟨U, hU, h⟩ := ih
    refine ⟨U, hU, fun k hk g => ?_⟩
    simp only [Pi.smul_apply]
    rw [h k hk g]

end Cyc

section MultOne

variable {F : Type*} [CommRing F]

def repOn (S : Submodule ℂ (GL (Fin 3) F → ℂ))
    (hS : ∀ (g : GL (Fin 3) F) (f : GL (Fin 3) F → ℂ), f ∈ S → gl3AmbientRightTranslate (R := ℂ) g f ∈ S) :
    GL (Fin 3) F →* Module.End ℂ S where
  toFun g := (gl3AmbientRightTranslate (R := ℂ) g).restrict (fun f hf => hS g f hf)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    show (f : GL (Fin 3) F → ℂ) (h * 1) = (f : GL (Fin 3) F → ℂ) h
    rw [mul_one]
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    show (f : GL (Fin 3) F → ℂ) (h * (g₁ * g₂)) = (f : GL (Fin 3) F → ℂ) (h * g₁ * g₂)
    rw [mul_assoc]

theorem gl3CyclicRep_eq_repOn (W : GL (Fin 3) F → ℂ) :
    gl3CyclicRep W = repOn (gl3CyclicSubspace W)
      (fun g _ hf => LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_mem_gl3CyclicSubspace W g hf) :=
  rfl

theorem multOne_repOn_iff_of_eq (ψ : AddChar F ℂ) {S₁ S₂ : Submodule ℂ (GL (Fin 3) F → ℂ)} (h : S₁ = S₂)
    (h₁ : ∀ (g : GL (Fin 3) F) (f : GL (Fin 3) F → ℂ), f ∈ S₁ → gl3AmbientRightTranslate (R := ℂ) g f ∈ S₁)
    (h₂ : ∀ (g : GL (Fin 3) F) (f : GL (Fin 3) F → ℂ), f ∈ S₂ → gl3AmbientRightTranslate (R := ℂ) g f ∈ S₂) :
    GL3WhittakerUniquenessStatement (repOn S₁ h₁) ψ ↔ GL3WhittakerUniquenessStatement (repOn S₂ h₂) ψ := by
  subst h
  rfl

theorem hasWhittakerMultOne_of_cyc_eq (ψ : AddChar F ℂ) {W X : GL (Fin 3) F → ℂ}
    (h : gl3CyclicSubspace X = gl3CyclicSubspace W) (hW : HasWhittakerMultOne ψ W) :
    HasWhittakerMultOne ψ X := by
  unfold HasWhittakerMultOne at hW ⊢
  rw [gl3CyclicRep_eq_repOn] at hW ⊢
  exact (multOne_repOn_iff_of_eq ψ h _ _).mpr hW

end MultOne

section Concl

variable (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
  (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
  (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ) (a₁ a₂ : ℂ)
  (W₂ W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)

def Concl32 :
    letI := localGLBorel ℚ v
    Measure (GL (Fin 2) (v.adicCompletion ℚ)) → Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range →
      (LocalGL3 v → ℂ) → Prop :=
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  fun μ₂ μN X =>
    ∃ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 ∧ qd ≠ 0 ∧
      (∀ s : ℂ, σ₂ < s.re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (X (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (dualWhittakerFn3 X (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(ℓ : ℤ)))) * W₂d g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₂ < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => X (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 X (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
          pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) ∧
      (∀ s : ℂ,
        pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            Ed.eval (a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                s))) *
            Ed.eval (a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                s))) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) *
            E.eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            E.eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            ε ^ 2)

variable {v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d}

theorem integral_smul_comp {α β : Type*} [MeasurableSpace α] (ν : Measure α) (c : ℂ) (X : β → ℂ) (ι : α → β)
    (B M : α → ℂ) :
    ∫ a, (c • X) (ι a) * B a * M a ∂ν = c * ∫ a, X (ι a) * B a * M a ∂ν := by
  rw [← integral_const_mul]; congr 1; funext a; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem integral_dual_smul_comp {α : Type*} [MeasurableSpace α] (ν : Measure α) (c : ℂ) (X : LocalGL3 v → ℂ)
    (ι : α → LocalGL3 v) (B M : α → ℂ) :
    ∫ a, dualWhittakerFn3 (c • X) (ι a) * B a * M a ∂ν = c * ∫ a, dualWhittakerFn3 X (ι a) * B a * M a ∂ν := by
  rw [← integral_const_mul]; congr 1; funext a
  simp only [dualWhittakerFn3_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem concl32_smul
    (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (μN : @Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range
      (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v)))
    {X : LocalGL3 v → ℂ} (hX : Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN X) (c : ℂ) :
    Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN (c • X) := by
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  obtain ⟨p, q, pd, qd, σ₂, σ₃, hq, hqd, hint, hintd, hid, hidd, hfe⟩ := hX
  refine ⟨Polynomial.C c * p, q, Polynomial.C c * pd, qd, σ₂, σ₃, hq, hqd, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have h := (hint s hs).const_mul c
    refine h.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro s hs
    have h := (hintd s hs).const_mul c
    refine h.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [dualWhittakerFn3, Pi.smul_apply, smul_eq_mul]
    ring
  · intro s hs
    have h := hid s hs
    simp only [RSCarrier.rsLocalIntegral] at h ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_C, ← h, integral_smul_comp]
    ring
  · intro s hs
    have h := hidd s hs
    simp only [RSCarrier.rsLocalIntegral] at h ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_C, ← h, integral_dual_smul_comp]
    ring
  · intro s
    have h := hfe s
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination c * h

theorem concl32_add
    (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (μN : @Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range
      (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v)))
    {X Y : LocalGL3 v → ℂ} (hX : Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN X)
    (hY : Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN Y) :
    Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN (X + Y) := by
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  obtain ⟨p, q, pd, qd, σ₂, σ₃, hq, hqd, hint, hintd, hid, hidd, hfe⟩ := hX
  obtain ⟨p', q', pd', qd', σ₂', σ₃', hq', hqd', hint', hintd', hid', hidd', hfe'⟩ := hY
  refine ⟨p * q' + p' * q, q * q', pd * qd' + pd' * qd, qd * qd', max σ₂ σ₂', max σ₃ σ₃',
    mul_ne_zero hq hq', mul_ne_zero hqd hqd', ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have h := (hint s (lt_of_le_of_lt (le_max_left _ _) hs)).add (hint' s (lt_of_le_of_lt (le_max_right _ _) hs))
    refine h.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [Pi.add_apply]
    ring
  · intro s hs
    have h := (hintd s (lt_of_le_of_lt (le_max_left _ _) hs)).add
      (hintd' s (lt_of_le_of_lt (le_max_right _ _) hs))
    refine h.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [dualWhittakerFn3, Pi.add_apply]
    ring
  · intro s hs
    have hs₁ : σ₂ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ₂' < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have h := hid s hs₁
    have h' := hid' s hs₂
    have hI := hint s hs₁
    have hI' := hint' s hs₂
    simp only [RSCarrier.rsLocalIntegral] at h h' ⊢
    have hsplit : (∫ g, ((X + Y) (iotaGL g) * W₂ g) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
          (s - 1 / 2) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) =
        (∫ g, (X (iotaGL g) * W₂ g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
            (s - 1 / 2) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) +
        ∫ g, (Y (iotaGL g) * W₂ g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
            (s - 1 / 2) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) := by
      rw [← integral_add hI hI']
      congr 1
      funext g
      simp only [Pi.add_apply]
      ring
    rw [hsplit, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul]
    linear_combination (q'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) * h +
      (q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) * h'
  · intro s hs
    have hs₁ : σ₃ < (1 - s).re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ₃' < (1 - s).re := lt_of_le_of_lt (le_max_right _ _) hs
    have h := hidd s hs₁
    have h' := hidd' s hs₂
    have hI := hintd s hs₁
    have hI' := hintd' s hs₂
    simp only [RSCarrier.rsLocalIntegral] at h h' ⊢
    have hsplit : (∫ g, (dualWhittakerFn3 (X + Y) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))) * W₂d g) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
          (1 - s - 1 / 2) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) =
        (∫ g, (dualWhittakerFn3 X (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))) * W₂d g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
            (1 - s - 1 / 2) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) +
        ∫ g, (dualWhittakerFn3 Y (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))) * W₂d g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^
            (1 - s - 1 / 2) ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) := by
      rw [← integral_add hI hI']
      congr 1
      funext g
      simp only [dualWhittakerFn3, Pi.add_apply]
      ring
    rw [hsplit, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul]
    linear_combination (qd'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) * h +
      (qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) * h'
  · intro s
    have h := hfe s
    have h' := hfe' s
    simp only [Polynomial.eval_add, Polynomial.eval_mul]
    linear_combination
      (qd'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * q'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) * h +
      (qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) * h'

theorem concl32_zero
    (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (μN : @Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range
      (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v))) :
    Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN 0 := by
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  refine ⟨0, 1, 0, 1, 0, 0, one_ne_zero, one_ne_zero, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    refine (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun g => ?_)
    simp
  · intro s hs
    refine (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun g => ?_)
    simp [dualWhittakerFn3]
  · intro s hs
    simp [RSCarrier.rsLocalIntegral]
  · intro s hs
    simp [RSCarrier.rsLocalIntegral, dualWhittakerFn3]
  · intro s; simp

theorem concl32_of_add_of
    (μ₂ : @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
    (μN : @Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range
      (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v)))
    {X Y : LocalGL3 v → ℂ} (hXY : Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN (X + Y))
    (hY : Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN Y) :
    Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN X := by
  have h := concl32_add μ₂ μN hXY (concl32_smul μ₂ μN hY (-1))
  have hfun : X + Y + (-1 : ℂ) • Y = X := by
    funext g; simp
  rwa [hfun] at h

end Concl

end P2primeTransport

end

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))) :
    ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
    (hW₂1 : W₂ 1 = 1)
    (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m)
    (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * (a₁ + a₂) / (a₁ * a₂))
        ((Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂)) m),
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    ∀ W' ∈ gl3CyclicSubspace W,
    ∃ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 ∧ qd ≠ 0 ∧
      (∀ s : ℂ, σ₂ < s.re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W' (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (dualWhittakerFn3 W' (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(ℓ : ℤ)))) * W₂d g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₂ < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W' (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 W' (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
          pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) ∧
      (∀ s : ℂ,
        pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            Ed.eval (a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                s))) *
            Ed.eval (a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 -
                s))) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) *
            E.eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            E.eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            ε ^ 2) := by
  intro a₁ a₂ ha W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT
  intro μ₂ hμ₂ μN hμN
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v

  suffices key : ∀ X ∈ gl3CyclicSubspace W, P2primeTransport.Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN X by
    intro W' hW'
    exact key W' hW'

  have hlawX : ∀ X ∈ gl3CyclicSubspace W, IsGL3PsiWhittakerFn ψv X := by
    intro X hX
    have := P2primeTransport.law_of_mem (X₀ := (v.adicCompletion ℚ) × (v.adicCompletion ℚ) × (v.adicCompletion ℚ))
      W (fun t => upperUnipotent3 t.1 t.2.1 t.2.2) (fun t => ψv (t.1 + t.2.1)) (fun t g => hW t.1 t.2.1 t.2.2 g) X hX
    intro x y z g
    exact this ⟨x, y, z⟩ g
  have hωX : ∀ X ∈ gl3CyclicSubspace W, ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      X (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * X h :=
    P2primeTransport.law_of_mem W (fun t => Matrix.GeneralLinearGroup.scalar (Fin 3) t)
      (fun t => ((ωv t : ℂˣ) : ℂ)) hω
  have hsmX := P2primeTransport.smooth_of_mem W hsm
  have h31X := LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
    v W E Ed ε ℓ h31

  have main : ∀ X ∈ gl3CyclicSubspace W, X 1 ≠ 0 →
      P2primeTransport.Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN X := by
    intro X hX hX1
    set c : ℂ := X 1 with hc
    set Xn : LocalGL3 v → ℂ := c⁻¹ • X with hXn
    have hXnmem : Xn ∈ gl3CyclicSubspace W := Submodule.smul_mem _ _ hX
    have hXn1 : Xn 1 = 1 := by
      simp only [hXn, Pi.smul_apply, smul_eq_mul]
      exact inv_mul_cancel₀ hX1
    have hXeq : X = c • Xn := by
      funext g
      simp only [hXn, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hX1, one_mul]

    have hXn0 : Xn ≠ 0 := by
      intro h0; rw [h0] at hXn1; simp at hXn1
    have hcycle : gl3CyclicSubspace Xn = gl3CyclicSubspace W := by
      refine le_antisymm (P2primeTransport.cyc_le_of_mem hXnmem) ?_
      exact P2primeTransport.cyc_le_of_mem (hirr Xn hXnmem hXn0)
    have hirrXn : ∀ F' ∈ gl3CyclicSubspace Xn, F' ≠ 0 → Xn ∈ gl3CyclicSubspace F' := by
      intro F' hF' hF'0
      rw [hcycle] at hF'
      exact P2primeTransport.cyc_le_of_mem (hirr F' hF' hF'0) hXnmem
    have hadmXn : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
        ∃ B : Finset (LocalGL3 v → ℂ), ∀ F' ∈ gl3CyclicSubspace Xn,
          (∀ k ∈ Uv, ∀ g : LocalGL3 v, F' (g * k) = F' g) → F' ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
      intro Uv hUv
      obtain ⟨B, hB⟩ := hadm Uv hUv
      exact ⟨B, fun F' hF' => hB F' (hcycle ▸ hF')⟩
    have hmultXn : HasWhittakerMultOne ψv Xn := P2primeTransport.hasWhittakerMultOne_of_cyc_eq ψv hcycle hmult
    have hnorm := LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge v ψv hψinv Xn
      (hlawX Xn hXnmem) hXn1 hmultXn hirrXn (hsmX Xn hXnmem) hadmXn
      ((LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3 W hWgauge Xn hXnmem).1) ωv hωu (hωX Xn hXnmem) hπ hϖ E Ed ε ℓ
      (h31X Xn hXnmem) a₁ a₂ ha W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT μ₂ μN
    have hC : P2primeTransport.Concl32 v hπ E Ed ε ℓ a₁ a₂ W₂ W₂d μ₂ μN Xn := hnorm
    rw [hXeq]
    exact P2primeTransport.concl32_smul μ₂ μN hC c

  intro X hX
  by_cases hX1 : X 1 ≠ 0
  · exact main X hX hX1
  push Not at hX1
  by_cases hW0 : W = 0
  · subst hW0
    have hX0 : X = 0 := by
      have : X ∈ (⊥ : Submodule ℂ (LocalGL3 v → ℂ)) := by
        rw [← LanglandsTunnell.CubicInduction.gl3CyclicSubspace_zero]; exact hX
      exact (Submodule.mem_bot ℂ).mp this
    rw [hX0]
    exact P2primeTransport.concl32_zero μ₂ μN
  · obtain ⟨h₀, hh₀⟩ : ∃ h₀, W h₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hW0 (funext hcon)
    set X₀ : LocalGL3 v → ℂ := fun g => W (g * h₀) with hX₀
    have hX₀mem : X₀ ∈ gl3CyclicSubspace W := P2primeTransport.self_translate_mem W h₀
    have hX₀1 : X₀ 1 ≠ 0 := by simpa [hX₀] using hh₀
    have hsum1 : (X + X₀) 1 ≠ 0 := by
      simp only [Pi.add_apply, hX1, zero_add]; exact hX₀1
    exact P2primeTransport.concl32_of_add_of μ₂ μN
      (main (X + X₀) (Submodule.add_mem _ hX hX₀mem) hsum1) (main X₀ hX₀mem hX₀1)

end S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_rsLocalIntegral_fe32_of_forall_localZeta31_fe_of_gauge (solution)
