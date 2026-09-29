-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a21f23df-ddb5-59e9-9a25-c4a6c14af43b

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_iotaGL_jacquetIntegral_eq_mul_integral_localZeta31
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_primalMiddleDatum_rsLocalIntegral_mul_eq_of_iotaGL_invariant_of_dominant
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant
import Theorems.Thm_LanglandsTunnell_CubicInduction_middleDatum_compare_of_primalMiddleDatum_of_dualMiddleDatum_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome"
p2m_attr_erase "simp" "LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

open LanglandsTunnell.CubicInduction

noncomputable section

namespace Ws1
namespace Middle

theorem exists_middle_of_halves (q ε : ℂ) (Z D E₁ E₂ Ed₁ Ed₂ : ℂ → ℂ)
    (m₁P m₂P : Polynomial ℂ) (kP : ℤ) (σP : ℝ) (hm₂P : m₂P ≠ 0)
    (hP : ∀ s : ℂ, σP < s.re →
      Z s * E₁ s * E₂ s * m₂P.eval (q ^ (-s)) = m₁P.eval (q ^ (-s)) * q ^ ((kP : ℂ) * s))
    (m₁d m₂d : Polynomial ℂ) (kd : ℤ) (σD : ℝ) (hm₂d : m₂d ≠ 0)
    (hD : ∀ s : ℂ, σD < (1 - s).re →
      D s * Ed₁ s * Ed₂ s * m₂d.eval (q ^ (-s)) = m₁d.eval (q ^ (-s)) * q ^ ((kd : ℂ) * s))
    (hG : ∀ s : ℂ, m₁d.eval (q ^ (-s)) * q ^ ((kd : ℂ) * s) * m₂P.eval (q ^ (-s)) =
      ε ^ 2 * (m₁P.eval (q ^ (-s)) * q ^ ((kP : ℂ) * s)) * m₂d.eval (q ^ (-s))) :
    ∃ (m₁ m₂ : Polynomial ℂ) (k : ℤ) (σP σD : ℝ), m₂ ≠ 0 ∧
      (∀ s : ℂ, σP < s.re →
        Z s * E₁ s * E₂ s * m₂.eval (q ^ (-s)) = m₁.eval (q ^ (-s)) * q ^ ((k : ℂ) * s)) ∧
      (∀ s : ℂ, σD < (1 - s).re →
        D s * Ed₁ s * Ed₂ s * m₂.eval (q ^ (-s)) = ε ^ 2 * (m₁.eval (q ^ (-s)) * q ^ ((k : ℂ) * s))) := by
  refine ⟨m₁P * m₂d, m₂P * m₂d, kP, σP, σD, mul_ne_zero hm₂P hm₂d, fun s hs => ?_, fun s hs => ?_⟩
  · rw [Polynomial.eval_mul, Polynomial.eval_mul]
    linear_combination (m₂d.eval (q ^ (-s))) * hP s hs
  · rw [Polynomial.eval_mul, Polynomial.eval_mul]
    linear_combination (m₂P.eval (q ^ (-s))) * hD s hs + hG s

end Ws1.Middle

namespace Ws1
namespace Middle
namespace DualKit

open scoped Topology ENNReal NNReal

section Haar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

scoped instance borelSpace_units_adic : BorelSpace (v.adicCompletion ℚ)ˣ := borelSpace_units

scoped instance isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

scoped instance isHaarMeasure_mulHaar :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) : Measure (v.adicCompletion ℚ)ˣ).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure ℚ v (selfDualHaarAt ℚ v)

end Haar

end Ws1.Middle.DualKit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1.Middle.DualKit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1.Middle"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1"

namespace Ws1
namespace Middle
namespace IntGlue

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem deformed_ne_zero {a₁ a₂ : ℂ} (ha : a₁ * a₂ ≠ 0) (u : ℂ) :
    (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) ≠ 0 := by
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega)
  have hpow : ∀ w : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ w ≠ 0 := fun w h => hN ((Complex.cpow_eq_zero_iff _ _).1 h).1
  exact mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul ha) (hpow _)) (mul_ne_zero (right_ne_zero_of_mul ha) (hpow _))

theorem exists_abscissa_integrable
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (ℓ : ℕ) (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
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
        ((Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂)) m)
    :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
    (∃ σ : ℝ, ∀ s : ℂ, σ < (1 - s).re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(ℓ : ℤ)))) * W₂d g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) := by
  subst hψinv
  intro μ₂ _ μN _
  obtain ⟨p, q, pd, qd, σ₂, σ₃, -, -, h1, h2, -, -⟩ :=
    LanglandsTunnell.CubicInduction.exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn
      v hπ hϖ W hW hsm hadm ℓ a₁ a₂ ha W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT μ₂ μN
  exact ⟨⟨σ₂, h1⟩, ⟨σ₃, h2⟩⟩

end Ws1.Middle.IntGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1.Middle.DualKit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1.Middle.DualKit"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1 P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1.Middle P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge.Ws1.Middle.DualKit"

set_option maxHeartbeats 12000000 in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
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
    ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0),
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∀ u : ℂ, ‖a₁‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-u.re) < ‖a₂‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u.re →
      ∀ (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
    (hW₂1 : W₂ 1 = 1)
    (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) + (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) / (Ideal.absNorm v.asIdeal : ℂ)) m)
    (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) + (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)))
        ((Ideal.absNorm v.asIdeal : ℂ) / ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u))) m),
      ∃ (m₁ m₂ : Polynomial ℂ) (k : ℤ) (σP σD : ℝ), m₂ ≠ 0 ∧
      (∀ s : ℂ, σP < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂ *
            E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            E.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) *
            m₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          m₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℂ) * s)) ∧
      (∀ s : ℂ, σD < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
            Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) *
            m₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          ε ^ 2 * (m₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((k : ℂ) * s))) := by
  intro a₁ a₂ ha μ₂ _ μN _ u hu W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT
  letI := localBorel ℚ v
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  haveI : ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) : Measure (v.adicCompletion ℚ)ˣ).IsHaarMeasure := Ws1.Middle.DualKit.isHaarMeasure_mulHaar v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := Ws1.Middle.DualKit.isAddHaarMeasure_selfDualHaarAt v

  obtain ⟨V, hVmem, hVK, hVdK, hKA⟩ :=
    LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
      v ψv hψinv W hW hsm hπ ℓ
  obtain ⟨cK, hcK, hK1⟩ :=
    LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_iotaGL_jacquetIntegral_eq_mul_integral_localZeta31
      v μ₂ μN (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)

  obtain ⟨⟨σ1, hσ1⟩, ⟨σ2, hσ2⟩⟩ := Ws1.Middle.IntGlue.exists_abscissa_integrable v ψv hψinv W hW hsm hadm hπ hϖ ℓ
    (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)
    (Ws1.Middle.IntGlue.deformed_ne_zero v ha u)
    W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT μ₂ μN
  obtain ⟨m₁P, m₂P, kP, σP, hm₂P, hPd, hP⟩ :=
    LanglandsTunnell.CubicInduction.exists_primalMiddleDatum_rsLocalIntegral_mul_eq_of_iotaGL_invariant_of_dominant v ψv hψinv W hW hW1 hmult hirr hsm hadm hWgauge ωv hωu hω hπ hϖ E Ed ε ℓ h31 V hVmem hVK hVdK a₁ a₂ ha μ₂ μN cK hcK hK1 u hu W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T
  obtain ⟨m₁d, m₂d, kd, σD, hm₂d, hDd, hD⟩ :=
    LanglandsTunnell.CubicInduction.exists_dualMiddleDatum_rsLocalIntegral_dual_mul_eq_of_iotaGL_invariant_of_dominant v ψv hψinv W hW hW1 hmult hirr hsm hadm hWgauge ωv hωu hω hπ hϖ E Ed ε ℓ h31 V hVmem hVK hVdK a₁ a₂ ha μ₂ μN cK hcK hK1 u hu W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT
  refine Ws1.Middle.exists_middle_of_halves (Ideal.absNorm v.asIdeal : ℂ) ε
    (fun s => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂)
    (fun s => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d)
    (fun s => E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))))
    (fun s => E.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))))
    (fun s => Ed.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))))
    (fun s => Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))))
    m₁P m₂P kP (max σP σ1) hm₂P (fun s hs => ?_) m₁d m₂d kd (max σD σ2) hm₂d (fun s hs => ?_)
    (LanglandsTunnell.CubicInduction.middleDatum_compare_of_primalMiddleDatum_of_dualMiddleDatum_of_ne_zero v ψv hψinv W hW hW1 hmult hirr hsm hadm hWgauge ωv hωu hω hπ hϖ E Ed ε ℓ h31 V hVmem hVK hVdK a₁ a₂ u _ ha hcK m₁P m₂P kP m₁d m₂d kd hPd hDd)
  · have hs₁ : σP < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ1 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    beta_reduce
    rw [((hKA μ₂ μN s).1 W₂ hW₂ψ hW₂K (hσ1 s hs₂)).2]
    exact hP s hs₁
  · have hs₁ : σD < (1 - s).re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ2 < (1 - s).re := lt_of_le_of_lt (le_max_right _ _) hs
    beta_reduce
    rw [((hKA μ₂ μN (1 - s)).2 W₂d hW₂dψ hW₂dK (hσ2 s hs₂)).2]
    exact hD s hs₁

end
end S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_mul_eq_and_dual_mul_eq_middle_of_dominant_of_forall_localZeta31_fe_of_gauge (solution)
