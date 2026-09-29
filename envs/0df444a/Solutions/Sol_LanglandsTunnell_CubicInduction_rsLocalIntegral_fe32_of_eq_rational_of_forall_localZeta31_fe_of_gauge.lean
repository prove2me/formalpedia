-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6e4467db-46d3-5b74-a484-dce4483085f1

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocal_fe32_of_rsLocal_fe32_of_eq_rational
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
import Theorems.Thm_MvPolynomial_eq_of_forall_eval_rpow_eq
import Theorems.Thm_MvPolynomial_eq_of_forall_rpow_infinite_setOf_eval_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_dominant_rsLocalIntegral_deformedSpherical_eq_and_fe_of_forall_localZeta31_fe_of_gauge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit'"
p2m_attr_erase "instance" "RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply"
p2m_attr_erase "simp" "M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

open LanglandsTunnell.CubicInduction

namespace BprimeS45

open MvPolynomial

theorem mv_eq_of_forall_mem_forall_mem_eval_eq {K : Type*} [CommRing K] [IsDomain K]
    (P Q : MvPolynomial (Fin 2) K) (S T : Set K) (hS : S.Infinite) (hT : T.Infinite)
    (h : ∀ x ∈ S, ∀ y ∈ T, MvPolynomial.eval ![x, y] P = MvPolynomial.eval ![x, y] Q) :
    P = Q := by
  refine MvPolynomial.funext_set ![S, T] (fun i => by fin_cases i <;> simpa) ?_
  intro v hv
  have h0 : v 0 ∈ S := by simpa using hv 0 (Set.mem_univ _)
  have h1 : v 1 ∈ T := by simpa using hv 1 (Set.mem_univ _)
  have hv' : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv']; exact h _ h0 _ h1

theorem eval_aeval_X_C {K : Type*} [CommRing K] (P : MvPolynomial (Fin 2) K) (x y : K) :
    Polynomial.eval x (MvPolynomial.aeval ![Polynomial.X, Polynomial.C y] P) =
      MvPolynomial.eval ![x, y] P := by
  have key : (Polynomial.evalRingHom x).comp
      (MvPolynomial.aeval ![Polynomial.X, Polynomial.C y] :
        MvPolynomial (Fin 2) K →ₐ[K] Polynomial K).toRingHom = MvPolynomial.eval ![x, y] := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp
    · fin_cases i <;> simp
  exact congrArg (fun f : MvPolynomial (Fin 2) K →+* K => f P) key

theorem mv_eq_of_forall_mem_infinite_setOf_eval_eq {K : Type*} [CommRing K] [IsDomain K]
    [Infinite K] (P Q : MvPolynomial (Fin 2) K) (T : Set K) (hT : T.Infinite)
    (h : ∀ y ∈ T,
      Set.Infinite {x : K | MvPolynomial.eval ![x, y] P = MvPolynomial.eval ![x, y] Q}) :
    P = Q := by
  refine mv_eq_of_forall_mem_forall_mem_eval_eq P Q Set.univ T Set.infinite_univ hT ?_
  intro x _ y hy
  have hxy : MvPolynomial.aeval ![Polynomial.X, Polynomial.C y] P =
      MvPolynomial.aeval ![Polynomial.X, Polynomial.C y] Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (h y hy).mono ?_
    intro x' hx'
    simpa only [Set.mem_setOf_eq, eval_aeval_X_C] using hx'
  have := congrArg (Polynomial.eval x) hxy
  simpa only [eval_aeval_X_C] using this

theorem mv_eq_of_forall_eval_rpow_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (S : Set ℂ)
    (hS : S.Infinite) (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ x ∈ S, ∀ u : ℝ, u₀ < u →
      MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q) :
    P = Q := by
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set f : ℝ → ℂ := fun u => (((N : ℝ) ^ u : ℝ) : ℂ) with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have : (N : ℝ) ^ a = (N : ℝ) ^ b := by simpa [hf] using hab
    exact (Real.strictMono_rpow_of_base_gt_one hN').injective this
  have hT : (f '' Set.Ioi u₀).Infinite := (Set.Ioi_infinite u₀).image hfinj.injOn
  refine mv_eq_of_forall_mem_forall_mem_eval_eq P Q S (f '' Set.Ioi u₀) hS hT ?_
  rintro x hx _ ⟨u, hu, rfl⟩
  exact h x hx u hu

theorem mv_eq_of_forall_rpow_infinite_setOf_eval_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ u : ℝ, u₀ < u →
      Set.Infinite {x : ℂ | MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q}) :
    P = Q := by
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set f : ℝ → ℂ := fun u => (((N : ℝ) ^ u : ℝ) : ℂ) with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have : (N : ℝ) ^ a = (N : ℝ) ^ b := by simpa [hf] using hab
    exact (Real.strictMono_rpow_of_base_gt_one hN').injective this
  have hT : (f '' Set.Ioi u₀).Infinite := (Set.Ioi_infinite u₀).image hfinj.injOn
  refine mv_eq_of_forall_mem_infinite_setOf_eval_eq P Q (f '' Set.Ioi u₀) hT ?_
  rintro _ ⟨u, hu, rfl⟩
  exact h u hu

theorem natCast_cpow_neg_ne_zero (N : ℕ) (hN : 1 < N) (s : ℂ) : (N : ℂ) ^ (-s) ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  left
  exact_mod_cast (show N ≠ 0 by omega)

theorem ofReal_rpow_natCast (N : ℕ) (u : ℝ) :
    (((N : ℝ) ^ u : ℝ) : ℂ) = (N : ℂ) ^ (u : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg N)]
  norm_cast

theorem natCast_cpow_neg_ofReal (N : ℕ) (t : ℝ) :
    (N : ℂ) ^ (-(t : ℂ)) = (((N : ℝ) ^ (-t) : ℝ) : ℂ) := by
  rw [ofReal_rpow_natCast]
  norm_cast

theorem ofReal_rpow_natCast_ne_zero (N : ℕ) (hN : 1 < N) (u : ℝ) :
    (((N : ℝ) ^ u : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < (N : ℝ) ^ u := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) u
  exact_mod_cast this.ne'

theorem norm_natCast_cpow_neg (N : ℕ) (hN : 1 < N) (s : ℂ) :
    ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem infinite_image_cpow_neg_halfPlane (N : ℕ) (hN : 1 < N) (σ : ℝ) :
    Set.Infinite ((fun s : ℂ => (N : ℂ) ^ (-s)) '' {s : ℂ | σ < s.re}) := by
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hinj : Function.Injective (fun t : ℝ => (((N : ℝ) ^ (-t) : ℝ) : ℂ)) := by
    intro a b hab
    dsimp only at hab
    have h1 : (N : ℝ) ^ (-a) = (N : ℝ) ^ (-b) := by exact_mod_cast hab
    have h2 := (Real.strictMono_rpow_of_base_gt_one hN').injective h1
    linarith
  have hsub : ((fun t : ℝ => (((N : ℝ) ^ (-t) : ℝ) : ℂ)) '' Set.Ioi σ) ⊆
      ((fun s : ℂ => (N : ℂ) ^ (-s)) '' {s : ℂ | σ < s.re}) := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨(t : ℂ), by simpa using ht, ?_⟩
    simp only [natCast_cpow_neg_ofReal]
  exact ((Set.Ioi_infinite σ).image hinj.injOn).mono hsub

theorem infinite_setOf_of_forall_lt_re (N : ℕ) (hN : 1 < N) (σ : ℝ) (p : ℂ → Prop)
    (h : ∀ s : ℂ, σ < s.re → p ((N : ℂ) ^ (-s))) : Set.Infinite {x : ℂ | p x} :=
  (infinite_image_cpow_neg_halfPlane N hN σ).mono (by rintro _ ⟨s, hs, rfl⟩; exact h s hs)

theorem exists_forall_lt_re_eval_cpow_neg_ne_zero (N : ℕ) (hN : 1 < N) (D : Polynomial ℂ)
    (hD : D ≠ 0) : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → D.eval ((N : ℂ) ^ (-s)) ≠ 0 := by
  classical

  obtain ⟨δ, hδ, hroot⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ D.roots, r ≠ 0 → δ ≤ ‖r‖ := by
    let T : Finset ℝ := (D.roots.toFinset.filter (· ≠ 0)).image (‖·‖)
    by_cases hT : T.Nonempty
    · refine ⟨T.min' hT, ?_, ?_⟩
      · obtain ⟨r, hr, hr'⟩ := Finset.mem_image.1 (T.min'_mem hT)
        rw [← hr']
        exact norm_pos_iff.2 (Finset.mem_filter.1 hr).2
      · intro r hr hr0
        exact T.min'_le _ (Finset.mem_image.2
          ⟨r, Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hr, hr0⟩, rfl⟩)
    · refine ⟨1, one_pos, ?_⟩
      intro r hr hr0
      exact absurd ⟨‖r‖, Finset.mem_image.2
        ⟨r, Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hr, hr0⟩, rfl⟩⟩ hT
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((N : ℝ)⁻¹) ^ n < δ :=
    exists_pow_lt_of_lt_one hδ (inv_lt_one_of_one_lt₀ hN')
  refine ⟨n, fun s hs h0 => ?_⟩
  have hx0 : (N : ℂ) ^ (-s) ≠ 0 := natCast_cpow_neg_ne_zero N hN s
  have hmem : (N : ℂ) ^ (-s) ∈ D.roots := (Polynomial.mem_roots hD).2 h0
  have h1 : δ ≤ ‖(N : ℂ) ^ (-s)‖ := hroot _ hmem hx0
  have h2 : ‖(N : ℂ) ^ (-s)‖ < δ := by
    rw [norm_natCast_cpow_neg N hN]
    calc (N : ℝ) ^ (-s.re) < (N : ℝ) ^ (-(n : ℝ)) :=
          (Real.rpow_lt_rpow_left_iff hN').2 (by linarith)
      _ = ((N : ℝ)⁻¹) ^ n := by rw [Real.rpow_neg hNpos.le, Real.rpow_natCast, inv_pow]
      _ < δ := hn
  linarith

def LRep (f : ℂ → ℂ → ℂ) : Prop :=
  ∃ (M : MvPolynomial (Fin 2) ℂ) (A B : ℕ),
    ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → f x y * x ^ A * y ^ B = MvPolynomial.eval ![x, y] M

namespace LRep

theorem const (c : ℂ) : LRep fun _ _ => c :=
  ⟨MvPolynomial.C c, 0, 0, by intro x y _ _; simp⟩

theorem fst : LRep fun x _ => x :=
  ⟨MvPolynomial.X 0, 0, 0, by intro x y _ _; simp⟩

theorem snd : LRep fun _ y => y :=
  ⟨MvPolynomial.X 1, 0, 0, by intro x y _ _; simp⟩

theorem fst_inv : LRep fun x _ => x⁻¹ :=
  ⟨1, 1, 0, by intro x y hx _; simp [hx]⟩

theorem snd_inv : LRep fun _ y => y⁻¹ :=
  ⟨1, 0, 1, by intro x y _ hy; simp [hy]⟩

theorem add {f g : ℂ → ℂ → ℂ} (hf : LRep f) (hg : LRep g) :
    LRep fun x y => f x y + g x y := by
  obtain ⟨M, A, B, hM⟩ := hf
  obtain ⟨M', A', B', hM'⟩ := hg
  refine ⟨M * (X 0 ^ A' * X 1 ^ B') + M' * (X 0 ^ A * X 1 ^ B), A + A', B + B',
    fun x y hx hy => ?_⟩
  simp only [map_add, map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [← hM x y hx hy, ← hM' x y hx hy]
  ring

theorem mul {f g : ℂ → ℂ → ℂ} (hf : LRep f) (hg : LRep g) :
    LRep fun x y => f x y * g x y := by
  obtain ⟨M, A, B, hM⟩ := hf
  obtain ⟨M', A', B', hM'⟩ := hg
  refine ⟨M * M', A + A', B + B', fun x y hx hy => ?_⟩
  simp only [map_mul]
  rw [← hM x y hx hy, ← hM' x y hx hy]
  ring

theorem neg {f : ℂ → ℂ → ℂ} (hf : LRep f) : LRep fun x y => -f x y := by
  have := (const (-1)).mul hf
  refine (this.elim fun M h => ⟨M, ?_⟩)
  obtain ⟨A, B, h⟩ := h
  exact ⟨A, B, fun x y hx hy => by rw [← h x y hx hy]; ring⟩

theorem sub {f g : ℂ → ℂ → ℂ} (hf : LRep f) (hg : LRep g) :
    LRep fun x y => f x y - g x y := by
  have := hf.add hg.neg
  obtain ⟨M, A, B, h⟩ := this
  exact ⟨M, A, B, fun x y hx hy => by rw [← h x y hx hy]; ring⟩

theorem pow {f : ℂ → ℂ → ℂ} (hf : LRep f) (n : ℕ) : LRep fun x y => f x y ^ n := by
  induction n with
  | zero => simpa using const 1
  | succ n ih =>
    obtain ⟨M, A, B, h⟩ := ih.mul hf
    exact ⟨M, A, B, fun x y hx hy => by rw [← h x y hx hy]; ring⟩

theorem const_mul {f : ℂ → ℂ → ℂ} (c : ℂ) (hf : LRep f) : LRep fun x y => c * f x y :=
  (const c).mul hf

theorem zpow_fst (i : ℤ) : LRep fun x _ => x ^ i := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · obtain ⟨M, A, B, h⟩ := fst.pow n
    exact ⟨M, A, B, fun x y hx hy => by beta_reduce; rw [zpow_natCast]; exact h x y hx hy⟩
  · refine ⟨1, n, 0, fun x y hx _ => ?_⟩
    simp [zpow_neg, zpow_natCast, hx]

theorem zpow_snd (j : ℤ) : LRep fun _ y => y ^ j := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · obtain ⟨M, A, B, h⟩ := snd.pow n
    exact ⟨M, A, B, fun x y hx hy => by beta_reduce; rw [zpow_natCast]; exact h x y hx hy⟩
  · refine ⟨1, 0, n, fun x y _ hy => ?_⟩
    simp [zpow_neg, zpow_natCast, hy]

theorem monomial (a : ℂ) (i j : ℤ) : LRep fun x y => a * x ^ i * y ^ j :=
  ((const a).mul (zpow_fst i)).mul (zpow_snd j)

theorem polynomial_eval {g : ℂ → ℂ → ℂ} (hg : LRep g) (E : Polynomial ℂ) :
    LRep fun x y => E.eval (g x y) := by
  induction E using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact hp.add hq
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    exact (const a).mul (hg.pow n)

theorem polynomial_eval_monomial (E : Polynomial ℂ) (a : ℂ) (i j : ℤ) :
    LRep fun x y => E.eval (a * x ^ i * y ^ j) :=
  (monomial a i j).polynomial_eval E

theorem mvPolynomial_eval {g₁ g₂ : ℂ → ℂ → ℂ} (h₁ : LRep g₁) (h₂ : LRep g₂)
    (P : MvPolynomial (Fin 2) ℂ) :
    LRep fun x y => MvPolynomial.eval ![g₁ x y, g₂ x y] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using const a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    fin_cases i
    · simpa using hp.mul h₁
    · simpa using hp.mul h₂

theorem mvPolynomial_eval_self (P : MvPolynomial (Fin 2) ℂ) :
    LRep fun x y => MvPolynomial.eval ![x, y] P :=
  mvPolynomial_eval fst snd P

theorem mvPolynomial_eval_inv_fst (c : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    LRep fun x y => MvPolynomial.eval ![c * x⁻¹, y] P :=
  mvPolynomial_eval ((const c).mul fst_inv) snd P

theorem mvPolynomial_eval_monomial (P : MvPolynomial (Fin 2) ℂ) (a b : ℂ) (i j k l : ℤ) :
    LRep fun x y => MvPolynomial.eval ![a * x ^ i * y ^ j, b * x ^ k * y ^ l] P :=
  mvPolynomial_eval (monomial a i j) (monomial b k l) P

end LRep

theorem eq_of_LRep_of_forall_cpow_neg_rpow (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (f g : ℂ → ℂ → ℂ)
    (hf : LRep f) (hg : LRep g)
    (h : ∀ s : ℂ, ∀ u : ℝ, u₀ < u →
      f ((N : ℂ) ^ (-s)) (((N : ℝ) ^ u : ℝ) : ℂ) = g ((N : ℂ) ^ (-s)) (((N : ℝ) ^ u : ℝ) : ℂ)) :
    ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → f x y = g x y := by
  obtain ⟨M, A, B, hM⟩ := hf
  obtain ⟨M', A', B', hM'⟩ := hg
  have key : M * (X 0 ^ A' * X 1 ^ B') = M' * (X 0 ^ A * X 1 ^ B) := by
    refine mv_eq_of_forall_eval_rpow_eq N hN u₀ (Set.range fun s : ℂ => (N : ℂ) ^ (-s)) ?_ _ _ ?_
    · exact (infinite_image_cpow_neg_halfPlane N hN 0).mono (Set.image_subset_range _ _)
    · rintro _ ⟨s, rfl⟩ u hu
      have hx : (N : ℂ) ^ (-s) ≠ 0 := natCast_cpow_neg_ne_zero N hN s
      have hy : (((N : ℝ) ^ u : ℝ) : ℂ) ≠ 0 := ofReal_rpow_natCast_ne_zero N hN u
      simp only [map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hM _ _ hx hy, ← hM' _ _ hx hy, h s u hu]
      ring
  intro x y hx hy
  have e := congrArg (MvPolynomial.eval ![x, y]) key
  simp only [map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one] at e
  rw [← hM x y hx hy, ← hM' x y hx hy] at e
  have hne : x ^ A * y ^ B * (x ^ A' * y ^ B') ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy))
      (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy))
  have : (f x y - g x y) * (x ^ A * y ^ B * (x ^ A' * y ^ B')) = 0 := by
    linear_combination e
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem eq_of_LRep_of_forall_exists_forall_lt_re (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
    (f g : ℂ → ℂ → ℂ) (hf : LRep f) (hg : LRep g)
    (h : ∀ u : ℝ, u₀ < u → ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      f ((N : ℂ) ^ (-s)) (((N : ℝ) ^ u : ℝ) : ℂ) = g ((N : ℂ) ^ (-s)) (((N : ℝ) ^ u : ℝ) : ℂ)) :
    ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → f x y = g x y := by
  obtain ⟨M, A, B, hM⟩ := hf
  obtain ⟨M', A', B', hM'⟩ := hg
  have key : M * (X 0 ^ A' * X 1 ^ B') = M' * (X 0 ^ A * X 1 ^ B) := by
    refine mv_eq_of_forall_rpow_infinite_setOf_eval_eq N hN u₀ _ _ fun u hu => ?_
    obtain ⟨σ, hσ⟩ := h u hu
    refine infinite_setOf_of_forall_lt_re N hN σ
      (fun x => MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] (M * (X 0 ^ A' * X 1 ^ B')) =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] (M' * (X 0 ^ A * X 1 ^ B))) fun s hs => ?_
    have hx : (N : ℂ) ^ (-s) ≠ 0 := natCast_cpow_neg_ne_zero N hN s
    have hy : (((N : ℝ) ^ u : ℝ) : ℂ) ≠ 0 := ofReal_rpow_natCast_ne_zero N hN u
    simp only [map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hM _ _ hx hy, ← hM' _ _ hx hy, hσ s hs]
    ring
  intro x y hx hy
  have e := congrArg (MvPolynomial.eval ![x, y]) key
  simp only [map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one] at e
  rw [← hM x y hx hy, ← hM' x y hx hy] at e
  have hne : x ^ A * y ^ B * (x ^ A' * y ^ B') ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy))
      (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy))
  have : (f x y - g x y) * (x ^ A * y ^ B * (x ^ A' * y ^ B')) = 0 := by
    linear_combination e
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem natCast_cpow_neg_one_sub (N : ℕ) (hN : 1 < N) (s : ℂ) :
    (N : ℂ) ^ (-(1 - s)) = (N : ℂ)⁻¹ * ((N : ℂ) ^ (-s))⁻¹ := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [show (-(1 - s) : ℂ) = (-1) + s by ring, Complex.cpow_add _ _ hN0, Complex.cpow_neg_one,
    Complex.cpow_neg, inv_inv]

theorem natCast_cpow_neg_add_half (N : ℕ) (hN : 1 < N) (s : ℂ) :
    (N : ℂ) ^ (-(s + 1 / 2)) = (N : ℂ) ^ (-(1 / 2 : ℂ)) * (N : ℂ) ^ (-s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [show (-(s + 1 / 2) : ℂ) = -(1 / 2 : ℂ) + -s by ring, Complex.cpow_add _ _ hN0]

theorem natCast_cpow_neg_half_sub (N : ℕ) (hN : 1 < N) (s : ℂ) :
    (N : ℂ) ^ (-(1 / 2 - s)) = (N : ℂ) ^ (-(1 / 2 : ℂ)) * ((N : ℂ) ^ (-s))⁻¹ := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [show (-(1 / 2 - s) : ℂ) = -(1 / 2 : ℂ) + s by ring, Complex.cpow_add _ _ hN0,
    ← inv_inv ((N : ℂ) ^ s), ← Complex.cpow_neg]

theorem ofReal_rpow_natCast_inv (N : ℕ) (u : ℝ) :
    ((((N : ℝ) ^ u : ℝ) : ℂ))⁻¹ = (((N : ℝ) ^ (-u) : ℝ) : ℂ) := by
  rw [Real.rpow_neg (Nat.cast_nonneg N), Complex.ofReal_inv]

theorem ofReal_rpow_mul_cpow_neg (N : ℕ) (hN : 1 < N) (u : ℝ) (s : ℂ) :
    (((N : ℝ) ^ u : ℝ) : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ ((u : ℂ) - s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [ofReal_rpow_natCast, sub_eq_add_neg, Complex.cpow_add _ _ hN0]

theorem natCast_cpow_half_sub (N : ℕ) (hN : 1 < N) (s : ℂ) :
    (N : ℂ) ^ (1 / 2 - s) = (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (-s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0]

theorem natCast_cpow_neg_sq (N : ℕ) (hN : 1 < N) (s : ℂ) :
    ((N : ℂ) ^ (-s)) ^ 2 = (N : ℂ) ^ (-(2 * s)) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [sq, ← Complex.cpow_add _ _ hN0]
  ring_nf

theorem natCast_cpow_ofReal_mul_cpow_neg_ofReal (N : ℕ) (hN : 1 < N) (u : ℝ) :
    (N : ℂ) ^ (u : ℂ) * (N : ℂ) ^ (-(u : ℂ)) = 1 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [← Complex.cpow_add _ _ hN0, add_neg_cancel, Complex.cpow_zero]

theorem mul_ofReal_rpow_neg_eq_mul_inv (N : ℕ) (a : ℂ) (u : ℝ) :
    a * (((N : ℝ) ^ (-u) : ℝ) : ℂ) = a * ((((N : ℝ) ^ u : ℝ) : ℂ))⁻¹ := by
  rw [ofReal_rpow_natCast_inv]

theorem ofReal_rpow_one_add (N : ℕ) (hN : 1 < N) (u : ℝ) :
    (((N : ℝ) ^ (1 + u) : ℝ) : ℂ) = (N : ℂ) * (((N : ℝ) ^ u : ℝ) : ℂ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  rw [Real.rpow_add hNpos, Real.rpow_one]
  push_cast
  ring

theorem exists_forall_lt_re_mul_eval_eq_of_deformation (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
    (F : ℝ → ℂ → ℂ) (p q R D : MvPolynomial (Fin 2) ℂ)
    (h1 : ∀ u : ℝ, u₀ < u → ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F u s * MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] q =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] p)
    (h2 : ∀ u : ℝ, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F u s * MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] D =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] R)
    (hD1 : MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] D ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F 0 s * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] q =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] p := by

  have key : p * D = R * q := by
    refine mv_eq_of_forall_rpow_infinite_setOf_eval_eq N hN u₀ _ _ fun u hu => ?_
    obtain ⟨σ1, h1'⟩ := h1 u hu
    obtain ⟨σ2, h2'⟩ := h2 u
    refine infinite_setOf_of_forall_lt_re N hN (max σ1 σ2)
      (fun x => MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] (p * D) =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] (R * q)) fun s hs => ?_
    have e1 := h1' s (lt_of_le_of_lt (le_max_left _ _) hs)
    have e2 := h2' s (lt_of_le_of_lt (le_max_right _ _) hs)
    simp only [map_mul]
    rw [← e1, ← e2]
    ring

  obtain ⟨σ0, h0⟩ := h2 0
  obtain ⟨σD, hD⟩ := exists_forall_lt_re_eval_cpow_neg_ne_zero N hN _ hD1
  refine ⟨max σ0 σD, fun s hs => ?_⟩
  have e0 := h0 s (lt_of_le_of_lt (le_max_left _ _) hs)
  simp only [Real.rpow_zero, Complex.ofReal_one] at e0
  have eD := hD s (lt_of_le_of_lt (le_max_right _ _) hs)
  rw [eval_aeval_X_C] at eD
  have ek := congrArg (MvPolynomial.eval ![(N : ℂ) ^ (-s), (1 : ℂ)]) key
  simp only [map_mul] at ek
  apply mul_right_cancel₀ eD
  calc F 0 s * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] q * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] D
      = F 0 s * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] D *
          MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] q := by ring
    _ = MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] R * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] q := by
          rw [e0]
    _ = MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] p * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] D :=
          ek.symm

theorem aeval_X_C_ne_zero_of_exists_eval_ne_zero (q : MvPolynomial (Fin 2) ℂ) (y : ℂ)
    (h : ∃ x : ℂ, MvPolynomial.eval ![x, y] q ≠ 0) :
    MvPolynomial.aeval ![Polynomial.X, Polynomial.C y] q ≠ 0 := by
  obtain ⟨x, hx⟩ := h
  intro h0
  apply hx
  rw [← eval_aeval_X_C, h0, Polynomial.eval_zero]

theorem aeval_X_C_one_ne_zero_of_exists_eval_ne_zero (q : MvPolynomial (Fin 2) ℂ)
    (h : ∃ x : ℂ, MvPolynomial.eval ![x, 1] q ≠ 0) :
    MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] q ≠ 0 :=
  aeval_X_C_ne_zero_of_exists_eval_ne_zero q 1 h

theorem eval_at_one_eq_polynomial_eval (q : MvPolynomial (Fin 2) ℂ) (x : ℂ) :
    MvPolynomial.eval ![x, 1] q =
      Polynomial.eval x (MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] q) :=
  (eval_aeval_X_C q x 1).symm

theorem exists_forall_lt_re_mul_eval_eq_of_deformation_LRep (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
    (F : ℝ → ℂ → ℂ) (p q : MvPolynomial (Fin 2) ℂ) (den num : ℂ → ℂ → ℂ)
    (hden : LRep den) (hnum : LRep num)
    (h1 : ∀ u : ℝ, u₀ < u → ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F u s * MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] q =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] p)
    (h2 : ∀ u : ℝ, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F u s * den ((N : ℂ) ^ (-s)) (((N : ℝ) ^ u : ℝ) : ℂ) =
        num ((N : ℂ) ^ (-s)) (((N : ℝ) ^ u : ℝ) : ℂ))
    (hden1 : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → den ((N : ℂ) ^ (-s)) 1 ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F 0 s * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] q =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] p := by
  obtain ⟨M, A, B, hM⟩ := hden
  obtain ⟨M', A', B', hM'⟩ := hnum

  let D : MvPolynomial (Fin 2) ℂ := M * (X 0 ^ A' * X 1 ^ B')
  let R : MvPolynomial (Fin 2) ℂ := M' * (X 0 ^ A * X 1 ^ B)
  have h2' : ∀ u : ℝ, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F u s * MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] D =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] R := by
    intro u
    obtain ⟨σ, hσ⟩ := h2 u
    refine ⟨σ, fun s hs => ?_⟩
    have hx : (N : ℂ) ^ (-s) ≠ 0 := natCast_cpow_neg_ne_zero N hN s
    have hy : (((N : ℝ) ^ u : ℝ) : ℂ) ≠ 0 := ofReal_rpow_natCast_ne_zero N hN u
    simp only [D, R, map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hM _ _ hx hy, ← hM' _ _ hx hy, ← hσ s hs]
    ring
  have hD1 : MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] D ≠ 0 := by
    obtain ⟨σ, hσ⟩ := hden1

    have hs : σ < (((σ + 1 : ℝ) : ℂ)).re := by simp
    apply aeval_X_C_ne_zero_of_exists_eval_ne_zero
    refine ⟨(N : ℂ) ^ (-((σ + 1 : ℝ) : ℂ)), ?_⟩
    have hx : (N : ℂ) ^ (-((σ + 1 : ℝ) : ℂ)) ≠ 0 := natCast_cpow_neg_ne_zero N hN _
    simp only [D, map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hM _ _ hx one_ne_zero]
    simp only [one_pow, mul_one]
    exact mul_ne_zero (mul_ne_zero (hσ _ hs) (pow_ne_zero _ hx)) (pow_ne_zero _ hx)
  exact exists_forall_lt_re_mul_eval_eq_of_deformation N hN u₀ F p q R D h1 h2' hD1

namespace LRep

theorem mvPolynomial_eval₃ {g₁ g₂ g₃ : ℂ → ℂ → ℂ} (h₁ : LRep g₁) (h₂ : LRep g₂) (h₃ : LRep g₃)
    (P : MvPolynomial (Fin 3) ℂ) :
    LRep fun x y => MvPolynomial.eval (![g₁ x y, g₂ x y, g₃ x y] : Fin 3 → ℂ) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using const a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    fin_cases i
    · simpa using hp.mul h₁
    · simpa using hp.mul h₂
    · simpa using hp.mul h₃

end LRep

theorem exists_forall_lt_re_and {P Q : ℂ → Prop}
    (hP : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → P s) (hQ : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Q s) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → P s ∧ Q s := by
  obtain ⟨σ₁, h₁⟩ := hP
  obtain ⟨σ₂, h₂⟩ := hQ
  exact ⟨max σ₁ σ₂, fun s hs =>
    ⟨h₁ s (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s (lt_of_le_of_lt (le_max_right _ _) hs)⟩⟩

theorem exists_forall_lt_re_eval_mul_cpow_neg_ne_zero (N : ℕ) (hN : 1 < N) (D : Polynomial ℂ)
    (hD : D.eval 0 ≠ 0) (a : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → D.eval (a * (N : ℂ) ^ (-s)) ≠ 0 := by

  have hne : D.comp (Polynomial.C a * Polynomial.X) ≠ 0 := by
    intro h0
    apply hD
    have := congrArg (Polynomial.eval 0) h0
    simpa [Polynomial.eval_comp] using this
  obtain ⟨σ, hσ⟩ := exists_forall_lt_re_eval_cpow_neg_ne_zero N hN _ hne
  refine ⟨σ, fun s hs => ?_⟩
  have := hσ s hs
  simpa [Polynomial.eval_comp] using this

theorem exists_forall_lt_re_eval_mul_cpow_neg_sq_ne_zero (N : ℕ) (hN : 1 < N) (D : Polynomial ℂ)
    (hD : D.eval 0 ≠ 0) (a : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → D.eval (a * ((N : ℂ) ^ (-s)) ^ 2) ≠ 0 := by
  have hne : D.comp (Polynomial.C a * Polynomial.X ^ 2) ≠ 0 := by
    intro h0
    apply hD
    have := congrArg (Polynomial.eval 0) h0
    simpa [Polynomial.eval_comp] using this
  obtain ⟨σ, hσ⟩ := exists_forall_lt_re_eval_cpow_neg_ne_zero N hN _ hne
  refine ⟨σ, fun s hs => ?_⟩
  have := hσ s hs
  simpa [Polynomial.eval_comp] using this

theorem exists_forall_lt_norm_mul_rpow_neg_lt (N : ℕ) (hN : 1 < N) (a₁ a₂ : ℂ) (ha₂ : a₂ ≠ 0) :
    ∃ u₀ : ℝ, ∀ u : ℝ, u₀ < u → ‖a₁‖ * (N : ℝ) ^ (-u) < ‖a₂‖ * (N : ℝ) ^ u := by
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have ha₂' : 0 < ‖a₂‖ := norm_pos_iff.2 ha₂

  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((N : ℝ)⁻¹) ^ n < ‖a₂‖ / (‖a₁‖ + 1) :=
    exists_pow_lt_of_lt_one (div_pos ha₂' (by positivity)) (inv_lt_one_of_one_lt₀ hN')
  refine ⟨n, fun u hu => ?_⟩
  have hu0 : (0 : ℝ) ≤ u := le_trans (Nat.cast_nonneg n) hu.le
  have h1 : (N : ℝ) ^ (-u) < (N : ℝ) ^ (-(n : ℝ)) := (Real.rpow_lt_rpow_left_iff hN').2 (by linarith)
  have h2 : (N : ℝ) ^ (-(n : ℝ)) = ((N : ℝ)⁻¹) ^ n := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_natCast, inv_pow]
  have h3 : (1 : ℝ) ≤ (N : ℝ) ^ u := Real.one_le_rpow hN'.le hu0
  have h4 : ‖a₁‖ * (N : ℝ) ^ (-u) ≤ (‖a₁‖ + 1) * (N : ℝ) ^ (-u) :=
    mul_le_mul_of_nonneg_right (by linarith [norm_nonneg a₁]) (Real.rpow_nonneg hNpos.le _)
  have h5 : (‖a₁‖ + 1) * (N : ℝ) ^ (-u) < (‖a₁‖ + 1) * (‖a₂‖ / (‖a₁‖ + 1)) := by
    have : (N : ℝ) ^ (-u) < ‖a₂‖ / (‖a₁‖ + 1) := by linarith [h1, h2 ▸ hn]
    exact mul_lt_mul_of_pos_left this (by positivity)
  have h6 : (‖a₁‖ + 1) * (‖a₂‖ / (‖a₁‖ + 1)) = ‖a₂‖ := by
    field_simp
  have h7 : ‖a₂‖ ≤ ‖a₂‖ * (N : ℝ) ^ u := le_mul_of_one_le_right ha₂'.le h3
  linarith

theorem exists_forall_lt_norm_mul_rpow_neg_re_lt (N : ℕ) (hN : 1 < N) (a₁ a₂ : ℂ) (ha₂ : a₂ ≠ 0) :
    ∃ u₀ : ℝ, ∀ u : ℝ, u₀ < u →
      ‖a₁‖ * (N : ℝ) ^ (-((u : ℂ)).re) < ‖a₂‖ * (N : ℝ) ^ ((u : ℂ)).re := by
  obtain ⟨u₀, h⟩ := exists_forall_lt_norm_mul_rpow_neg_lt N hN a₁ a₂ ha₂
  exact ⟨u₀, fun u hu => by simpa only [Complex.ofReal_re] using h u hu⟩

end BprimeS45

namespace BprimeS45

namespace LRep

theorem congr_off_axes {f g : ℂ → ℂ → ℂ} (hf : LRep f)
    (h : ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → g x y = f x y) : LRep g := by
  obtain ⟨M, A, B, hM⟩ := hf
  exact ⟨M, A, B, fun x y hx hy => by rw [h x y hx hy]; exact hM x y hx hy⟩

theorem div_const {f : ℂ → ℂ → ℂ} (hf : LRep f) (c : ℂ) : LRep fun x y => f x y / c := by
  have h := hf.mul (const c⁻¹)
  simpa only [div_eq_mul_inv] using h

theorem inv_inv' {f : ℂ → ℂ → ℂ} (hf : LRep f) : LRep fun x y => (f x y)⁻¹⁻¹ := by
  simpa only [inv_inv] using hf

theorem inv_mul' {f g : ℂ → ℂ → ℂ} (hf : LRep fun x y => (f x y)⁻¹) (hg : LRep fun x y => (g x y)⁻¹) :
    LRep fun x y => (f x y * g x y)⁻¹ := by
  have h := hf.mul hg
  simpa only [mul_inv] using h

theorem inv_const (c : ℂ) : LRep fun _ _ => c⁻¹ := const c⁻¹

end LRep

theorem exists_forall_lt_re_mul_eval_eq_of_deformation₀ (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
    (F : ℝ → ℂ → ℂ) (F₀ : ℂ → ℂ) (p q R D : MvPolynomial (Fin 2) ℂ)
    (h1 : ∀ u : ℝ, u₀ < u → ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F u s * MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] q =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] p)
    (h2 : ∀ u : ℝ, u₀ < u → ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F u s * MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] D =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] R)
    (h0 : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F₀ s * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] D = MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] R)
    (hD1 : MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] D ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F₀ s * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] q =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] p := by

  have key : p * D = R * q := by
    refine mv_eq_of_forall_rpow_infinite_setOf_eval_eq N hN u₀ _ _ fun u hu => ?_
    obtain ⟨σ1, h1'⟩ := h1 u hu
    obtain ⟨σ2, h2'⟩ := h2 u hu
    refine infinite_setOf_of_forall_lt_re N hN (max σ1 σ2)
      (fun x => MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] (p * D) =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] (R * q)) fun s hs => ?_
    have e1 := h1' s (lt_of_le_of_lt (le_max_left _ _) hs)
    have e2 := h2' s (lt_of_le_of_lt (le_max_right _ _) hs)
    simp only [map_mul]
    rw [← e1, ← e2]
    ring

  obtain ⟨σ0, h0⟩ := h0
  obtain ⟨σD, hD⟩ := exists_forall_lt_re_eval_cpow_neg_ne_zero N hN _ hD1
  refine ⟨max σ0 σD, fun s hs => ?_⟩
  have e0 := h0 s (lt_of_le_of_lt (le_max_left _ _) hs)
  have eD := hD s (lt_of_le_of_lt (le_max_right _ _) hs)
  rw [eval_aeval_X_C] at eD
  have ek := congrArg (MvPolynomial.eval ![(N : ℂ) ^ (-s), (1 : ℂ)]) key
  simp only [map_mul] at ek
  apply mul_right_cancel₀ eD
  calc F₀ s * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] q * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] D
      = F₀ s * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] D *
          MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] q := by ring
    _ = MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] R * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] q := by
          rw [e0]
    _ = MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] p * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] D :=
          ek.symm

theorem exists_forall_lt_re_mul_eval_eq_of_deformation_LRep₀ (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
    (F : ℝ → ℂ → ℂ) (F₀ : ℂ → ℂ) (p q : MvPolynomial (Fin 2) ℂ) (den num : ℂ → ℂ → ℂ)
    (hden : LRep den) (hnum : LRep num)
    (h1 : ∀ u : ℝ, u₀ < u → ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F u s * MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] q =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] p)
    (h2 : ∀ u : ℝ, u₀ < u → ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F u s * den ((N : ℂ) ^ (-s)) (((N : ℝ) ^ u : ℝ) : ℂ) =
        num ((N : ℂ) ^ (-s)) (((N : ℝ) ^ u : ℝ) : ℂ))
    (h0 : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → F₀ s * den ((N : ℂ) ^ (-s)) 1 = num ((N : ℂ) ^ (-s)) 1)
    (hden1 : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → den ((N : ℂ) ^ (-s)) 1 ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F₀ s * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] q =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] p := by
  obtain ⟨M, A, B, hM⟩ := hden
  obtain ⟨M', A', B', hM'⟩ := hnum
  let D : MvPolynomial (Fin 2) ℂ := M * (MvPolynomial.X 0 ^ A' * MvPolynomial.X 1 ^ B')
  let R : MvPolynomial (Fin 2) ℂ := M' * (MvPolynomial.X 0 ^ A * MvPolynomial.X 1 ^ B)
  have h2' : ∀ u : ℝ, u₀ < u → ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F u s * MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] D =
        MvPolynomial.eval ![(N : ℂ) ^ (-s), (((N : ℝ) ^ u : ℝ) : ℂ)] R := by
    intro u hu
    obtain ⟨σ, hσ⟩ := h2 u hu
    refine ⟨σ, fun s hs => ?_⟩
    have hx : (N : ℂ) ^ (-s) ≠ 0 := natCast_cpow_neg_ne_zero N hN s
    have hy : (((N : ℝ) ^ u : ℝ) : ℂ) ≠ 0 := ofReal_rpow_natCast_ne_zero N hN u
    simp only [D, R, map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hM _ _ hx hy, ← hM' _ _ hx hy, ← hσ s hs]
    ring
  have h0' : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      F₀ s * MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] D = MvPolynomial.eval ![(N : ℂ) ^ (-s), 1] R := by
    obtain ⟨σ, hσ⟩ := h0
    refine ⟨σ, fun s hs => ?_⟩
    have hx : (N : ℂ) ^ (-s) ≠ 0 := natCast_cpow_neg_ne_zero N hN s
    simp only [D, R, map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hM _ _ hx one_ne_zero, ← hM' _ _ hx one_ne_zero, ← hσ s hs]
    ring
  have hD1 : MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] D ≠ 0 := by
    obtain ⟨σ, hσ⟩ := hden1
    have hs : σ < (((σ + 1 : ℝ) : ℂ)).re := by simp
    apply aeval_X_C_ne_zero_of_exists_eval_ne_zero
    refine ⟨(N : ℂ) ^ (-((σ + 1 : ℝ) : ℂ)), ?_⟩
    have hx : (N : ℂ) ^ (-((σ + 1 : ℝ) : ℂ)) ≠ 0 := natCast_cpow_neg_ne_zero N hN _
    simp only [D, map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hM _ _ hx one_ne_zero]
    simp only [one_pow, mul_one]
    exact mul_ne_zero (mul_ne_zero (hσ _ hs) (pow_ne_zero _ hx)) (pow_ne_zero _ hx)
  exact exists_forall_lt_re_mul_eval_eq_of_deformation₀ N hN u₀ F F₀ p q R D h1 h2' h0' hD1

end BprimeS45

noncomputable section

namespace Bp

open LanglandsTunnell.CubicInduction
open scoped Matrix

section Mat

variable {A : Type*} [CommRing A]

theorem transposeInv3_mul (a b : GL (Fin 3) A) : transposeInv3 (a * b) = transposeInv3 a * transposeInv3 b := by
  refine Units.ext ?_
  show (((a * b)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ =
    (((a⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ * (((b⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((transposeInv3 g)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = (g : Matrix (Fin 3) (Fin 3) A)
  show (((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ)ᵀ = (g : Matrix (Fin 3) (Fin 3) A)
  exact Matrix.transpose_transpose _

theorem dualWhittakerFn3_translate {R : Type*} (W : GL (Fin 3) A → R) (h g : GL (Fin 3) A) :
    dualWhittakerFn3 (fun x => W (x * h)) g = dualWhittakerFn3 W (g * transposeInv3 h) := by
  simp only [dualWhittakerFn3_apply]
  rw [transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc]

theorem dualWhittakerFn3_mul {R : Type*} (W : GL (Fin 3) A → R) (g z : GL (Fin 3) A) :
    dualWhittakerFn3 W (g * z) = dualWhittakerFn3 (fun x => W (x * transposeInv3 z)) g := by
  rw [dualWhittakerFn3_translate, transposeInv3_transposeInv3]

theorem scalarPi_comm {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) (g : GL (Fin 2) K) :
    scalarPi π hπ * g = g * scalarPi π hπ := by
  refine Units.ext ?_
  have h : ((scalarPi π hπ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = π • (1 : Matrix (Fin 2) (Fin 2) K) := by
    show (!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) K) = π • 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [Units.val_mul, Units.val_mul, h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem scalarPi_zpow_comm {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) (n : ℤ) (g : GL (Fin 2) K) :
    scalarPi π hπ ^ n * g = g * scalarPi π hπ ^ n :=
  ((show Commute (scalarPi π hπ) g from scalarPi_comm π hπ g).zpow_left n).eq

end Mat

section Cyc

variable {F : Type*} [CommRing F]

theorem isGL3PsiWhittakerFn_of_mem {ψ : AddChar F ℂ} {W W' : GL (Fin 3) F → ℂ}
    (hW : IsGL3PsiWhittakerFn ψ W) (h : W' ∈ gl3CyclicSubspace W) : IsGL3PsiWhittakerFn ψ W' := by
  have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace F ℂ ψ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ g ((mem_gl3PsiWhittakerFnSpace_iff ψ W).mpr hW)
  exact (mem_gl3PsiWhittakerFnSpace_iff ψ W').mp (hle h)

theorem gl3CyclicSubspace_le_of_mem {W W' : GL (Fin 3) F → ℂ} (h : W' ∈ gl3CyclicSubspace W) :
    gl3CyclicSubspace W' ≤ gl3CyclicSubspace W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, rfl⟩
  exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W g h

end Cyc

section Smooth

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem smooth_of_mem {W W' : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (h : W' ∈ gl3CyclicSubspace W) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W' (g * k) = W' g := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨U, hUo, hU⟩ := hsm
    refine ⟨U.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · have hc : Continuous fun x : LocalGL3 v => (MulAut.conj h⁻¹).toMonoidHom x := by
        show Continuous fun x : LocalGL3 v => h⁻¹ * x * h⁻¹⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const
      exact hUo.preimage hc
    · intro k hk g
      have hk' : h⁻¹ * k * h⁻¹⁻¹ ∈ U := hk
      show W (g * k * h) = W (g * h)
      have := hU _ hk' (g * h)
      rw [inv_inv] at this
      simpa only [mul_assoc, mul_inv_cancel_left] using this
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, hU₁o, hU₁⟩ := hx
    obtain ⟨U₂, hU₂o, hU₂⟩ := hy
    refine ⟨U₁ ⊓ U₂, hU₁o.inter hU₂o, fun k hk g => ?_⟩
    simp only [Pi.add_apply, hU₁ k hk.1 g, hU₂ k hk.2 g]
  | smul c x _ hx =>
    obtain ⟨U, hUo, hU⟩ := hx
    exact ⟨U, hUo, fun k hk g => by simp only [Pi.smul_apply, hU k hk g]⟩

end Smooth

end Bp

end

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
    ∀ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 → qd ≠ 0 →
      (∀ s : ℂ, σ₂ < s.re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) →
      (∀ s : ℂ, σ₃ < (1 - s).re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(ℓ : ℤ)))) * W₂d g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) →
      (∀ s : ℂ, σ₂ < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) →
      (∀ s : ℂ, σ₃ < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
          pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) →
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
  intro a₁ a₂ ha W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T W₂d hW₂dψ hW₂dK hW₂d1 hW₂dZ hW₂dT μ₂ _ μN _ p q pd qd σ₂ σ₃ hq hqd hint hintd hrat hratd
  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  have hN1 : 1 < (Ideal.absNorm v.asIdeal) := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hNC : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (show (Ideal.absNorm v.asIdeal) ≠ 0 by omega)
  have hNpow : ∀ w : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ w ≠ 0 := fun w h => hNC ((Complex.cpow_eq_zero_iff _ _).1 h).1
  have ha₁ : a₁ ≠ 0 := left_ne_zero_of_mul ha
  have ha₂ : a₂ ≠ 0 := right_ne_zero_of_mul ha

  obtain ⟨P, Q, Pd, Qd, hguard, hFE⟩ :=
    LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_dominant_rsLocalIntegral_deformedSpherical_eq_and_fe_of_forall_localZeta31_fe_of_gauge
      v ψv hψinv W hW hW1 hmult hirr hsm hadm hWgauge ωv hωu hω hπ hϖ E Ed ε ℓ h31 a₁ a₂ ha μ₂ μN

  obtain ⟨W'', hW''mem, hW''K, hW''Kd, hKavg⟩ :=
    LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
      v ψv hψinv W hW hsm hπ ℓ
  have hW''w : IsGL3PsiWhittakerFn ψv W'' := Bp.isGL3PsiWhittakerFn_of_mem hW hW''mem
  have hW''sm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W'' (g * k) = W'' g := Bp.smooth_of_mem v hsm hW''mem
  have hW''adm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W'',
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
    intro Uv hUv
    obtain ⟨B, hB⟩ := hadm Uv hUv
    exact ⟨B, fun F hF hFk => hB F (Bp.gl3CyclicSubspace_le_of_mem hW''mem hF) hFk⟩

  obtain ⟨P₁, D₁, D₂, e₁, hD₁0, hD₂0, hcell₁⟩ :=
    LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant
      v (NumberField.StandardAddChar.psiLocal ℚ v) (Or.inl rfl) hπ hϖ W'' (by rw [← hψinv]; exact hW''w) hW''K hW''sm hW''adm
  obtain ⟨c₁, hcell₁⟩ := hcell₁ μ₂ μN

  obtain ⟨hDsm, hDadm, hDw⟩ :=
    LanglandsTunnell.CubicInduction.admissible_gl3CyclicSubspace_dualWhittakerFn3_rightTranslate
      v W'' hW''sm hW''adm (transposeInv3 (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))))
  have hW'w : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹⁻¹ (dualWhittakerFn3 (fun x => W'' (x * transposeInv3 (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))))) := by
    have := hDw ψv hW''w
    rwa [hψinv] at this
  have hzK : ∀ k : GL (Fin 2) (v.adicCompletion ℚ), iotaGL k * (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))) = (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))) * iotaGL k := by
    intro k
    rw [← map_mul, ← map_mul, Bp.scalarPi_zpow_comm]
  have hW'K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 (fun x => W'' (x * transposeInv3 (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))))) (g * iotaGL k) =
        dualWhittakerFn3 (fun x => W'' (x * transposeInv3 (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))))) g := by
    intro k hk g
    rw [← Bp.dualWhittakerFn3_mul W'' (g * iotaGL k) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))), ← Bp.dualWhittakerFn3_mul W'' g (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))), mul_assoc, hzK k,
      ← mul_assoc, hW''Kd k hk]
  obtain ⟨P₂, D₁', D₂', e₂, hD₁'0, hD₂'0, hcell₂⟩ :=
    LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant
      v (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (Or.inr rfl) hπ hϖ (dualWhittakerFn3 (fun x => W'' (x * transposeInv3 (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))))) hW'w hW'K hDsm hDadm
  obtain ⟨c₂, hcell₂⟩ := hcell₂ μ₂ μN

  have hχ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → NumberField.StandardAddChar.psiLocal ℚ v x = 1 := fun x hx =>
    LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v x
      hx
  have hχ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x = 1 := fun x hx => by
    rw [AddChar.inv_apply, hχ (-x) (by rwa [Valuation.map_neg])]
  have hb : ∀ u : ℝ, a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((u : ℝ) : ℂ)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((u : ℝ) : ℂ)) ≠ 0 := fun u =>
    mul_ne_zero (mul_ne_zero ha₁ (hNpow _)) (mul_ne_zero ha₂ (hNpow _))
  have famP : ∀ u : ℝ, ∃ W₂u : GL (Fin 2) (v.adicCompletion ℚ) → ℂ,
      (∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)), W₂u (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂u g) ∧
      (∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂u (g * k) = W₂u g) ∧
      W₂u 1 = 1 ∧
      (∀ g : GL (Fin 2) (v.adicCompletion ℚ), W₂u (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((u : ℝ) : ℂ)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((u : ℝ) : ℂ)) / (Ideal.absNorm v.asIdeal : ℂ) * W₂u g) ∧
      (∀ m : ℤ, W₂u (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
        torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((u : ℝ) : ℂ)) + a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((u : ℝ) : ℂ)) (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((u : ℝ) : ℂ)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((u : ℝ) : ℂ)) / (Ideal.absNorm v.asIdeal : ℂ)) m) :=
    fun u => LanglandsTunnell.CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
      v (NumberField.StandardAddChar.psiLocal ℚ v) hχ hπ hϖ _ (div_ne_zero (hb u) hNC) _ _ _
  choose W₂f hW₂fψ hW₂fK hW₂f1 hW₂fZ hW₂fT using famP
  have famD : ∀ u : ℝ, ∃ W₂u : GL (Fin 2) (v.adicCompletion ℚ) → ℂ,
      (∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)), W₂u (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂u g) ∧
      (∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂u (g * k) = W₂u g) ∧
      W₂u 1 = 1 ∧
      (∀ g : GL (Fin 2) (v.adicCompletion ℚ), W₂u (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = (Ideal.absNorm v.asIdeal : ℂ) / (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((u : ℝ) : ℂ)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((u : ℝ) : ℂ))) * W₂u g) ∧
      (∀ m : ℤ, W₂u (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
        torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((u : ℝ) : ℂ)) + a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((u : ℝ) : ℂ)) / (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((u : ℝ) : ℂ)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((u : ℝ) : ℂ)))) ((Ideal.absNorm v.asIdeal : ℂ) / (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((u : ℝ) : ℂ)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((u : ℝ) : ℂ)))) m) :=
    fun u => LanglandsTunnell.CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
      v (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ hχ' hπ hϖ _ (div_ne_zero hNC (hb u)) _ _ _
  choose W₂df hW₂dfψ hW₂dfK hW₂df1 hW₂dfZ hW₂dfT using famD
  obtain ⟨u₀, hu₀⟩ := BprimeS45.exists_forall_lt_norm_mul_rpow_neg_re_lt (Ideal.absNorm v.asIdeal) hN1 a₁ a₂ ha₂

  have hxh : ∀ s : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s) = (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) :=
    fun s => BprimeS45.natCast_cpow_half_sub (Ideal.absNorm v.asIdeal) hN1 s
  have hyu : ∀ u : ℝ, (Ideal.absNorm v.asIdeal : ℂ) ^ ((u : ℝ) : ℂ) = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u : ℝ) : ℂ) := fun u => (BprimeS45.ofReal_rpow_natCast (Ideal.absNorm v.asIdeal) u).symm
  have hyu' : ∀ u : ℝ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-((u : ℝ) : ℂ)) = (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u : ℝ) : ℂ))⁻¹ := fun u => by
    rw [BprimeS45.natCast_cpow_neg_ofReal, BprimeS45.ofReal_rpow_natCast_inv]
  have hy0 : ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (0 : ℝ) : ℝ) : ℂ) = 1 := by rw [Real.rpow_zero, Complex.ofReal_one]

  have hy : ∀ u : ℝ, ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u : ℝ) : ℂ) ≠ 0 := fun u => BprimeS45.ofReal_rpow_natCast_ne_zero (Ideal.absNorm v.asIdeal) hN1 u
  have hx1 : ∀ s : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)) = (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ :=
    fun s => BprimeS45.natCast_cpow_neg_one_sub (Ideal.absNorm v.asIdeal) hN1 s
  have hxm : ∀ s : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)) = (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ :=
    fun s => BprimeS45.natCast_cpow_neg_half_sub (Ideal.absNorm v.asIdeal) hN1 s
  have hxp : ∀ s : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2)) = (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) :=
    fun s => BprimeS45.natCast_cpow_neg_add_half (Ideal.absNorm v.asIdeal) hN1 s
  have eZ : ∀ y : ℂ, y ≠ 0 → (Ideal.absNorm v.asIdeal : ℂ) / (a₁ * y⁻¹ * (a₂ * y)) = (Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ * y * ((Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹ * y⁻¹) / (Ideal.absNorm v.asIdeal : ℂ) := by
    intro y hy; field_simp
  have eT : ∀ y : ℂ, y ≠ 0 →
      (Ideal.absNorm v.asIdeal : ℂ) * (a₁ * y⁻¹ + a₂ * y) / (a₁ * y⁻¹ * (a₂ * y)) = (Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ * y + (Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹ * y⁻¹ := by
    intro y hy; field_simp; ring
  have eZ0 : (Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂) = (Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ * ((Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹) / (Ideal.absNorm v.asIdeal : ℂ) := by field_simp
  have eT0 : (Ideal.absNorm v.asIdeal : ℂ) * (a₁ + a₂) / (a₁ * a₂) = (Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ + (Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹ := by field_simp; ring

  have hFEu := fun (u : ℝ) (hu : u₀ < u) =>
    hFE (u : ℂ) (hu₀ u hu) (W₂f u) (hW₂fψ u) (hW₂fK u) (hW₂f1 u) (hW₂fZ u) (hW₂fT u)
      (W₂df u) (hW₂dfψ u) (hW₂dfK u) (hW₂df1 u) (hW₂dfZ u) (hW₂dfT u)

  have hWd : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      dualWhittakerFn3 (fun x => W'' (x * transposeInv3 (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))))) (iotaGL g) =
        dualWhittakerFn3 W'' (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ)))) :=
    fun g => (Bp.dualWhittakerFn3_mul W'' (iotaGL g) (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))).symm

  have hZ₀ : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂ * MvPolynomial.eval ![(Ideal.absNorm v.asIdeal : ℂ) ^ (-s), 1] Q = MvPolynomial.eval ![(Ideal.absNorm v.asIdeal : ℂ) ^ (-s), 1] P := by
    refine BprimeS45.exists_forall_lt_re_mul_eval_eq_of_deformation_LRep₀ (Ideal.absNorm v.asIdeal) hN1 u₀
      (fun u s => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) (W₂f u))
      (fun s => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂)
      P Q (fun x y => ((((Polynomial.eval (((a₁) * y⁻¹) * (((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) * x)) D₁) * (Polynomial.eval (((a₂) * y) * (((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) * x)) D₁)) * (Polynomial.eval (((((a₁) * y⁻¹) * ((a₂) * y)) / (Ideal.absNorm v.asIdeal : ℂ)) * ((((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) * x) ^ 2)) D₂)) * ((((((a₁) * y⁻¹) * ((a₂) * y)) / (Ideal.absNorm v.asIdeal : ℂ)) * ((((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) * x) ^ 2)) ^ e₁))) (fun x y => ((c₁) * (MvPolynomial.eval (![(((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) * x), ((a₁) * y⁻¹), ((a₂) * y)] : Fin 3 → ℂ) P₁)))
      (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.polynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const (a₁)) BprimeS45.LRep.snd_inv) (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))) BprimeS45.LRep.fst)) (D₁)) (BprimeS45.LRep.polynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const (a₂)) BprimeS45.LRep.snd) (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))) BprimeS45.LRep.fst)) (D₁))) (BprimeS45.LRep.polynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.div_const (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const (a₁)) BprimeS45.LRep.snd_inv) (BprimeS45.LRep.mul (BprimeS45.LRep.const (a₂)) BprimeS45.LRep.snd)) ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.pow (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))) BprimeS45.LRep.fst) (2))) (D₂))) (BprimeS45.LRep.pow (BprimeS45.LRep.mul (BprimeS45.LRep.div_const (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const (a₁)) BprimeS45.LRep.snd_inv) (BprimeS45.LRep.mul (BprimeS45.LRep.const (a₂)) BprimeS45.LRep.snd)) ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.pow (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))) BprimeS45.LRep.fst) (2))) (e₁)))
      (BprimeS45.LRep.mul (BprimeS45.LRep.const (c₁)) (BprimeS45.LRep.mvPolynomial_eval₃ (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))) BprimeS45.LRep.fst) (BprimeS45.LRep.mul (BprimeS45.LRep.const (a₁)) BprimeS45.LRep.snd_inv) (BprimeS45.LRep.mul (BprimeS45.LRep.const (a₂)) BprimeS45.LRep.snd) (P₁)))
      ?_ ?_ ?_ ?_
    ·
      intro u hu
      obtain ⟨σ₂', σ₃', hA, hB, hCc, hD, hE⟩ := hFEu u hu
      refine ⟨σ₂', fun s hs => ?_⟩
      have := hCc s hs
      rw [hyu u] at this
      exact this
    ·
      intro u hu
      obtain ⟨σ₂', σ₃', hA, hB, hCc, hD, hE⟩ := hFEu u hu
      obtain ⟨σ₀, h₀⟩ := hcell₁ (a₁ * (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u : ℝ) : ℂ))⁻¹) (a₂ * ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u : ℝ) : ℂ)) (W₂f u) (hW₂fψ u) (hW₂fK u)
        (fun g => by rw [hW₂fZ u g, hyu' u, hyu u]) (fun m => by rw [hW₂fT u m, hyu' u, hyu u])
      refine ⟨max σ₂' σ₀, fun s hs => ?_⟩
      obtain ⟨hI'', hEq⟩ := (hKavg μ₂ μN s).1 (W₂f u) (hW₂fψ u) (hW₂fK u) (hA s (lt_of_le_of_lt (le_max_left _ _) hs))
      have := h₀ s (lt_of_le_of_lt (le_max_right _ _) hs) hI''
      rw [← hEq, hxh s] at this
      exact this
    ·
      obtain ⟨σ₀, h₀⟩ := hcell₁ a₁ a₂ W₂ hW₂ψ hW₂K hW₂Z hW₂T
      refine ⟨max σ₂ σ₀, fun s hs => ?_⟩
      obtain ⟨hI'', hEq⟩ := (hKavg μ₂ μN s).1 W₂ hW₂ψ hW₂K (hint s (lt_of_le_of_lt (le_max_left _ _) hs))
      have := h₀ s (lt_of_le_of_lt (le_max_right _ _) hs) hI''
      rw [← hEq, hxh s] at this
      simp only [inv_one, mul_one]
      exact this
    ·
      obtain ⟨σa, hσa⟩ := BprimeS45.exists_forall_lt_re_eval_mul_cpow_neg_ne_zero (Ideal.absNorm v.asIdeal) hN1 D₁ hD₁0 (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))
      obtain ⟨σb, hσb⟩ := BprimeS45.exists_forall_lt_re_eval_mul_cpow_neg_ne_zero (Ideal.absNorm v.asIdeal) hN1 D₁ hD₁0 (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))
      obtain ⟨σc, hσc⟩ := BprimeS45.exists_forall_lt_re_eval_mul_cpow_neg_sq_ne_zero (Ideal.absNorm v.asIdeal) hN1 D₂ hD₂0
        (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) ^ 2)
      refine ⟨max (max σa σb) σc, fun s hs => ?_⟩
      have h1 := hσa s (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs)
      have h2 := hσb s (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs)
      have h3 := hσc s (lt_of_le_of_lt (le_max_right _ _) hs)
      simp only [inv_one, mul_one]
      rw [show a₁ * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) by ring,
        show a₂ * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) by ring,
        show a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 2 = a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) ^ 2 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 2 by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3)
        (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero ha₁ ha₂) hNC) (pow_ne_zero _ (hNpow _)))
          (pow_ne_zero _ (hNpow _))))

  have hD₀ : ∃ σ : ℝ, ∀ t : ℂ, σ < t.re →
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            t (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) W₂d * MvPolynomial.eval ![(Ideal.absNorm v.asIdeal : ℂ) ^ (-t), 1] Qd = MvPolynomial.eval ![(Ideal.absNorm v.asIdeal : ℂ) ^ (-t), 1] Pd := by
    refine BprimeS45.exists_forall_lt_re_mul_eval_eq_of_deformation_LRep₀ (Ideal.absNorm v.asIdeal) hN1 u₀
      (fun u t => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            t (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) (W₂df u))
      (fun t => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            t (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) W₂d)
      Pd Qd (fun x y => ((((Polynomial.eval (((((Ideal.absNorm v.asIdeal : ℂ)) * (a₁⁻¹)) * y) * (((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) * x)) D₁') * (Polynomial.eval (((((Ideal.absNorm v.asIdeal : ℂ)) * (a₂⁻¹)) * y⁻¹) * (((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) * x)) D₁')) * (Polynomial.eval (((((((Ideal.absNorm v.asIdeal : ℂ)) * (a₁⁻¹)) * y) * ((((Ideal.absNorm v.asIdeal : ℂ)) * (a₂⁻¹)) * y⁻¹)) / (Ideal.absNorm v.asIdeal : ℂ)) * ((((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) * x) ^ 2)) D₂')) * ((((((((Ideal.absNorm v.asIdeal : ℂ)) * (a₁⁻¹)) * y) * ((((Ideal.absNorm v.asIdeal : ℂ)) * (a₂⁻¹)) * y⁻¹)) / (Ideal.absNorm v.asIdeal : ℂ)) * ((((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) * x) ^ 2)) ^ e₂))) (fun x y => ((c₂) * (MvPolynomial.eval (![(((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) * x), ((((Ideal.absNorm v.asIdeal : ℂ)) * (a₁⁻¹)) * y), ((((Ideal.absNorm v.asIdeal : ℂ)) * (a₂⁻¹)) * y⁻¹)] : Fin 3 → ℂ) P₂)))
      (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.polynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.const (a₁⁻¹))) BprimeS45.LRep.snd) (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))) BprimeS45.LRep.fst)) (D₁')) (BprimeS45.LRep.polynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.const (a₂⁻¹))) BprimeS45.LRep.snd_inv) (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))) BprimeS45.LRep.fst)) (D₁'))) (BprimeS45.LRep.polynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.div_const (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.const (a₁⁻¹))) BprimeS45.LRep.snd) (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.const (a₂⁻¹))) BprimeS45.LRep.snd_inv)) ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.pow (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))) BprimeS45.LRep.fst) (2))) (D₂'))) (BprimeS45.LRep.pow (BprimeS45.LRep.mul (BprimeS45.LRep.div_const (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.const (a₁⁻¹))) BprimeS45.LRep.snd) (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.const (a₂⁻¹))) BprimeS45.LRep.snd_inv)) ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.pow (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))) BprimeS45.LRep.fst) (2))) (e₂)))
      (BprimeS45.LRep.mul (BprimeS45.LRep.const (c₂)) (BprimeS45.LRep.mvPolynomial_eval₃ (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))) BprimeS45.LRep.fst) (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.const (a₁⁻¹))) BprimeS45.LRep.snd) (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ))) (BprimeS45.LRep.const (a₂⁻¹))) BprimeS45.LRep.snd_inv) (P₂)))
      ?_ ?_ ?_ ?_
    ·
      intro u hu
      obtain ⟨σ₂', σ₃', hA, hB, hCc, hD, hE⟩ := hFEu u hu
      refine ⟨σ₃', fun t ht => ?_⟩
      have := hD (1 - t) (by rwa [sub_sub_cancel])
      rw [sub_sub_cancel, hyu u] at this
      exact this
    ·
      intro u hu
      obtain ⟨σ₂', σ₃', hA, hB, hCc, hD, hE⟩ := hFEu u hu
      obtain ⟨σ₀, h₀⟩ := hcell₂ ((Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ * ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u : ℝ) : ℂ)) ((Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹ * (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ u : ℝ) : ℂ))⁻¹) (W₂df u)
        (hW₂dfψ u) (hW₂dfK u)
        (fun g => by rw [hW₂dfZ u g, hyu' u, hyu u, eZ _ (hy u)])
        (fun m => by rw [hW₂dfT u m, hyu' u, hyu u, eT _ (hy u), eZ _ (hy u)])
      refine ⟨max σ₃' σ₀, fun t hs => ?_⟩
      have hBt := hB (1 - t) (by rw [sub_sub_cancel]; exact (lt_of_le_of_lt (le_max_left _ _) hs))
      rw [sub_sub_cancel] at hBt
      obtain ⟨hI'', hEq⟩ := (hKavg μ₂ μN t).2 (W₂df u) (hW₂dfψ u) (hW₂dfK u) hBt
      simp only [hWd] at h₀
      have := h₀ t (lt_of_le_of_lt (le_max_right _ _) hs) hI''
      rw [← hEq, hxh t] at this
      exact this
    ·
      obtain ⟨σ₀, h₀⟩ := hcell₂ ((Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹) ((Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹) W₂d hW₂dψ hW₂dK
        (fun g => by rw [hW₂dZ g, eZ0]) (fun m => by rw [hW₂dT m, eT0, eZ0])
      refine ⟨max σ₃ σ₀, fun t hs => ?_⟩
      have hBt := hintd (1 - t) (by rw [sub_sub_cancel]; exact (lt_of_le_of_lt (le_max_left _ _) hs))
      rw [sub_sub_cancel] at hBt
      obtain ⟨hI'', hEq⟩ := (hKavg μ₂ μN t).2 W₂d hW₂dψ hW₂dK hBt
      simp only [hWd] at h₀
      have := h₀ t (lt_of_le_of_lt (le_max_right _ _) hs) hI''
      rw [← hEq, hxh t] at this
      simp only [inv_one, mul_one]
      exact this
    ·
      obtain ⟨σa, hσa⟩ := BprimeS45.exists_forall_lt_re_eval_mul_cpow_neg_ne_zero (Ideal.absNorm v.asIdeal) hN1 D₁' hD₁'0 ((Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))
      obtain ⟨σb, hσb⟩ := BprimeS45.exists_forall_lt_re_eval_mul_cpow_neg_ne_zero (Ideal.absNorm v.asIdeal) hN1 D₁' hD₁'0 ((Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ))
      obtain ⟨σc, hσc⟩ := BprimeS45.exists_forall_lt_re_eval_mul_cpow_neg_sq_ne_zero (Ideal.absNorm v.asIdeal) hN1 D₂' hD₂'0
        ((Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ * ((Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹) / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) ^ 2)
      refine ⟨max (max σa σb) σc, fun s hs => ?_⟩
      have h1 := hσa s (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs)
      have h2 := hσb s (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs)
      have h3 := hσc s (lt_of_le_of_lt (le_max_right _ _) hs)
      simp only [inv_one, mul_one]
      rw [show (Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = (Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) by ring,
        show (Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹ * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = (Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) by ring,
        show (Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ * ((Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹) / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 2 =
          (Ideal.absNorm v.asIdeal : ℂ) * a₁⁻¹ * ((Ideal.absNorm v.asIdeal : ℂ) * a₂⁻¹) / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 : ℂ)) ^ 2 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 2 by ring]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3)
        (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero hNC (inv_ne_zero ha₁))
          (mul_ne_zero hNC (inv_ne_zero ha₂))) hNC) (pow_ne_zero _ (hNpow _))) (pow_ne_zero _ (hNpow _))))

  have hFE₁ : ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → ((((MvPolynomial.eval ![(((Ideal.absNorm v.asIdeal : ℂ)⁻¹) * x⁻¹), y] Pd) * (MvPolynomial.eval ![x, y] Q)) * (Polynomial.eval (((a₁) * y⁻¹)⁻¹ * (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))) * x⁻¹)) Ed)) * (Polynomial.eval (((a₂) * y)⁻¹ * (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))) * x⁻¹)) Ed)) = (((((MvPolynomial.eval ![x, y] P) * (MvPolynomial.eval ![(((Ideal.absNorm v.asIdeal : ℂ)⁻¹) * x⁻¹), y] Qd)) * (Polynomial.eval (((a₁) * y⁻¹) * (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))) * x)) E)) * (Polynomial.eval (((a₂) * y) * (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))) * x)) E)) * ((ε) ^ 2)) := by
    refine BprimeS45.eq_of_LRep_of_forall_cpow_neg_rpow (Ideal.absNorm v.asIdeal) hN1 u₀
      (fun x y => ((((MvPolynomial.eval ![(((Ideal.absNorm v.asIdeal : ℂ)⁻¹) * x⁻¹), y] Pd) * (MvPolynomial.eval ![x, y] Q)) * (Polynomial.eval (((a₁) * y⁻¹)⁻¹ * (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))) * x⁻¹)) Ed)) * (Polynomial.eval (((a₂) * y)⁻¹ * (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))) * x⁻¹)) Ed))) (fun x y => (((((MvPolynomial.eval ![x, y] P) * (MvPolynomial.eval ![(((Ideal.absNorm v.asIdeal : ℂ)⁻¹) * x⁻¹), y] Qd)) * (Polynomial.eval (((a₁) * y⁻¹) * (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))) * x)) E)) * (Polynomial.eval (((a₂) * y) * (((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ))) * x)) E)) * ((ε) ^ 2)))
      (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mvPolynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ)⁻¹)) BprimeS45.LRep.fst_inv) BprimeS45.LRep.snd (Pd)) (BprimeS45.LRep.mvPolynomial_eval BprimeS45.LRep.fst BprimeS45.LRep.snd (Q))) (BprimeS45.LRep.polynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.inv_mul' (BprimeS45.LRep.const (a₁⁻¹)) (BprimeS45.LRep.inv_inv' BprimeS45.LRep.snd)) (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)))) BprimeS45.LRep.fst_inv)) (Ed))) (BprimeS45.LRep.polynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.inv_mul' (BprimeS45.LRep.const (a₂⁻¹)) BprimeS45.LRep.snd_inv) (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)))) BprimeS45.LRep.fst_inv)) (Ed)))
      (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.mvPolynomial_eval BprimeS45.LRep.fst BprimeS45.LRep.snd (P)) (BprimeS45.LRep.mvPolynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ)⁻¹)) BprimeS45.LRep.fst_inv) BprimeS45.LRep.snd (Qd))) (BprimeS45.LRep.polynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const (a₁)) BprimeS45.LRep.snd_inv) (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)))) BprimeS45.LRep.fst)) (E))) (BprimeS45.LRep.polynomial_eval (BprimeS45.LRep.mul (BprimeS45.LRep.mul (BprimeS45.LRep.const (a₂)) BprimeS45.LRep.snd) (BprimeS45.LRep.mul (BprimeS45.LRep.const ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)))) BprimeS45.LRep.fst)) (E))) (BprimeS45.LRep.pow (BprimeS45.LRep.const (ε)) (2)))
      fun s u hu => ?_
    obtain ⟨σ₂', σ₃', hA, hB, hCc, hD, hE⟩ := hFEu u hu
    have := hE s
    rw [hx1 s, hxm s, hxp s, hyu' u, hyu u] at this
    exact this
  have hq₀ : (MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] Q) ≠ 0 := BprimeS45.aeval_X_C_one_ne_zero_of_exists_eval_ne_zero Q (hguard 1 one_ne_zero).1
  have hqd₀ : (MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] Qd) ≠ 0 := BprimeS45.aeval_X_C_one_ne_zero_of_exists_eval_ne_zero Qd (hguard 1 one_ne_zero).2
  have hFE₀ : ∀ s : ℂ,
      ((MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] Pd)).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) * ((MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] Q)).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
          Ed.eval (a₁⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) * Ed.eval (a₂⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) =
        ((MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] P)).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * ((MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] Qd)).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) *
          E.eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * E.eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * ε ^ 2 := by
    intro s
    have := hFE₁ ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) 1 (hNpow _) one_ne_zero
    simp only [inv_one, mul_one] at this
    rw [← BprimeS45.eval_at_one_eq_polynomial_eval Pd, ← BprimeS45.eval_at_one_eq_polynomial_eval Q,
      ← BprimeS45.eval_at_one_eq_polynomial_eval P, ← BprimeS45.eval_at_one_eq_polynomial_eval Qd,
      hx1 s, hxm s, hxp s]
    exact this
  obtain ⟨σp, hZ₀⟩ := hZ₀
  obtain ⟨σd, hD₀⟩ := hD₀
  exact LanglandsTunnell.RankinSelberg.forall_rsLocal_fe32_of_rsLocal_fe32_of_eq_rational
    (Ideal.absNorm v.asIdeal) hN1
    (fun s => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂)
    (fun s => RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) W₂d)
    E Ed ε a₁ a₂ (MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] P) (MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] Q) (MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] Pd) (MvPolynomial.aeval ![Polynomial.X, Polynomial.C (1 : ℂ)] Qd) σp σd hq₀ hqd₀
    (fun s hs => by
      rw [← BprimeS45.eval_at_one_eq_polynomial_eval Q, ← BprimeS45.eval_at_one_eq_polynomial_eval P]
      exact hZ₀ s hs)
    (fun s hs => by
      rw [← BprimeS45.eval_at_one_eq_polynomial_eval Qd, ← BprimeS45.eval_at_one_eq_polynomial_eval Pd]
      exact hD₀ (1 - s) hs)
    hFE₀ p q pd qd σ₂ σ₃ hq hqd hrat hratd

end S_LanglandsTunnell_CubicInduction_rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge (solution)
