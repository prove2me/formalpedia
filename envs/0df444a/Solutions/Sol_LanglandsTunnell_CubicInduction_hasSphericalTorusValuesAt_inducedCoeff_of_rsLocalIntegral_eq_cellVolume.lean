-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_inducedCoeff_of_rsLocalIntegral_eq_cellVolume
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a3453f81-fc68-55d7-b0d5-b70f123bea9b

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn_of_mem_congruenceK1
import Theorems.Thm_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three
import Theorems.Thm_LanglandsTunnell_CubicInduction_iotaGL_mem_congruenceK1_iff
import Theorems.Thm_LanglandsTunnell_CubicInduction_iotaGL_mem_localMaximalCompact3_of_mem_localLevelOne
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_LanglandsTunnell_RankinSelberg_mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Data.Complex.Basic
import Definitions.Def_HaarQuotient
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_ConstantTerm
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_inducedCoeff_of_rsLocalIntegral_eq_cellVolume
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

section FormalInverse

open scoped Topology

private theorem hasSum_coeff_mk_mul_coe_mul_pow (c : ℕ → ℂ) (Q : Polynomial ℂ) (z : ℂ)
    (hs : Summable fun n : ℕ => c n * z ^ n) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.mk c * (Q : PowerSeries ℂ)) * z ^ n)
      ((∑' n : ℕ, c n * z ^ n) * Q.eval z) := by
  set G : ℕ → ℂ := fun n => PowerSeries.coeff n (PowerSeries.mk c * (Q : PowerSeries ℂ)) with hG
  show HasSum (fun n : ℕ => G n * z ^ n) _
  set D := Q.natDegree with hD

  set u : ℕ → ℕ → ℂ := fun j n => if j ≤ n then c (n - j) * Q.coeff j * z ^ n else 0 with hu
  have hu_sum : ∀ j : ℕ, HasSum (u j) (Q.coeff j * z ^ j * ∑' n : ℕ, c n * z ^ n) := by
    intro j
    have hshift : HasSum (fun n : ℕ => u j (n + j)) (Q.coeff j * z ^ j * ∑' n : ℕ, c n * z ^ n) := by
      have h0 := hs.hasSum.mul_left (Q.coeff j * z ^ j)
      refine h0.congr_fun ?_
      intro n
      simp only [hu, Nat.le_add_left, if_true, Nat.add_sub_cancel, pow_add]
      ring
    have hzero : ∑ i ∈ Finset.range j, u j i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp [hu, not_le.mpr hi]
    have hshift' : HasSum (fun n : ℕ => u j (n + j))
        ((Q.coeff j * z ^ j * ∑' n : ℕ, c n * z ^ n) - ∑ i ∈ Finset.range j, u j i) := by
      rwa [hzero, sub_zero]
    exact (hasSum_nat_add_iff' j).mp hshift'

  have hG_eq : ∀ n : ℕ, G n * z ^ n = ∑ j ∈ Finset.range (D + 1), u j n := by
    intro n
    simp only [hG, PowerSeries.coeff_mul, PowerSeries.coeff_mk, Polynomial.coeff_coe, Finset.sum_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => c i * Q.coeff j * z ^ n)]
    simp only [Nat.succ_eq_add_one]
    rw [← Finset.sum_range_reflect]
    have hre : ∀ k ∈ Finset.range (n + 1),
        c (n + 1 - 1 - k) * Q.coeff (n - (n + 1 - 1 - k)) * z ^ n = c (n - k) * Q.coeff k * z ^ n := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega]
    rw [Finset.sum_congr rfl hre]

    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    symm
    refine Finset.sum_subset (f := fun k => c (n - k) * Q.coeff k * z ^ n) ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk.2)
    · intro k hk hk'
      simp only [Finset.mem_filter, Finset.mem_range, not_and] at hk hk'
      have hkD : D < k := by
        by_contra hle
        exact hk' (Nat.lt_succ_of_le (not_lt.mp hle)) (Nat.lt_succ_iff.mp hk)
      show c (n - k) * Q.coeff k * z ^ n = 0
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hD ▸ hkD)]
      ring

  have hfin := hasSum_sum (s := Finset.range (D + 1)) (f := fun j n => u j n)
    (a := fun j => Q.coeff j * z ^ j * ∑' n : ℕ, c n * z ^ n) (fun j _ => hu_sum j)
  have heval : Q.eval z = ∑ j ∈ Finset.range (D + 1), Q.coeff j * z ^ j := Polynomial.eval_eq_sum_range z
  have hval : (∑' n : ℕ, c n * z ^ n) * Q.eval z =
      ∑ j ∈ Finset.range (D + 1), Q.coeff j * z ^ j * ∑' n : ℕ, c n * z ^ n := by
    rw [heval, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hval, show (fun n : ℕ => G n * z ^ n) = fun n => ∑ j ∈ Finset.range (D + 1), u j n from funext hG_eq]
  exact hfin

private theorem tsum_mul_eval_eq_one_of_mk_mul_coe_eq_one (c : ℕ → ℂ) (Q : Polynomial ℂ) (z : ℂ)
    (hs : Summable fun n : ℕ => c n * z ^ n) (h : PowerSeries.mk c * (Q : PowerSeries ℂ) = 1) :
    (∑' n : ℕ, c n * z ^ n) * Q.eval z = 1 := by
  have h1 := hasSum_coeff_mk_mul_coe_mul_pow c Q z hs
  rw [h] at h1
  have h2 : HasSum (fun n : ℕ => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) 1 := by
    have hfun : (fun n : ℕ => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) =
        fun n : ℕ => if n = 0 then (1 : ℂ) else 0 := by
      funext n
      by_cases hn : n = 0
      · subst hn; simp
      · simp [PowerSeries.coeff_one, hn]
    rw [hfun]
    simpa using hasSum_ite_eq (0 : ℕ) (1 : ℂ)
  exact h1.unique h2

private theorem mk_mul_coe_eq_one_of_forall_tsum_mul_eval_eq_one (F : ℕ → ℂ) (P : Polynomial ℂ) {r : ℝ}
    (hr : 0 < r) (hsum : ∀ z : ℂ, ‖z‖ < r → Summable fun n : ℕ => F n * z ^ n)
    (h : ∀ z : ℂ, ‖z‖ < r → (∑' n : ℕ, F n * z ^ n) * P.eval z = 1) :
    PowerSeries.mk F * (P : PowerSeries ℂ) = 1 := by

  set G : ℕ → ℂ := fun n => PowerSeries.coeff n (PowerSeries.mk F * (P : PowerSeries ℂ)) with hG

  have hA : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => G n * z ^ n) ((∑' n : ℕ, F n * z ^ n) * P.eval z) :=
    fun z hz => hasSum_coeff_mk_mul_coe_mul_pow F P z (hsum z hz)

  have hB : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => G n * z ^ n) 1 := fun z hz => h z hz ▸ hA z hz

  have hC : ∀ n : ℕ, G n = if n = 0 then 1 else 0 := by
    set Gc : ℕ → ℂ := fun n => if n = 0 then (1 : ℂ) else 0 with hGc

    have hr2 : (0 : ℝ) < r / 2 := by positivity
    have hsumG : HasSum (fun n : ℕ => G n * ((r / 2 : ℝ) : ℂ) ^ n) 1 := by
      refine hB _ ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2]
      linarith
    have hradG : (0 : ENNReal) < (FormalMultilinearSeries.ofScalars ℂ G).radius := by
      refine lt_of_lt_of_le ?_
        ((FormalMultilinearSeries.ofScalars ℂ G).le_radius_of_tendsto (r := ⟨r / 2, hr2.le⟩) (l := 0) ?_)
      · exact ENNReal.coe_pos.mpr (by exact_mod_cast hr2)
      · have ht := hsumG.summable.tendsto_atTop_zero
        have ht' := ht.norm
        simp only [norm_zero, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2] at ht'
        simp [FormalMultilinearSeries.ofScalars_norm] at ht' ⊢
        exact ht'
    have hradGc : (0 : ENNReal) < (FormalMultilinearSeries.ofScalars ℂ Gc).radius := by
      refine lt_of_lt_of_le ?_
        ((FormalMultilinearSeries.ofScalars ℂ Gc).le_radius_of_bound (C := 1) (r := 1) ?_)
      · exact zero_lt_one
      · intro n
        rw [FormalMultilinearSeries.ofScalars_norm]
        cases n <;> simp [hGc]

    have h1 : HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ G).sum
        (FormalMultilinearSeries.ofScalars ℂ G) 0 :=
      ((FormalMultilinearSeries.ofScalars ℂ G).hasFPowerSeriesOnBall hradG).hasFPowerSeriesAt
    have h2 : HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ Gc).sum
        (FormalMultilinearSeries.ofScalars ℂ Gc) 0 :=
      ((FormalMultilinearSeries.ofScalars ℂ Gc).hasFPowerSeriesOnBall hradGc).hasFPowerSeriesAt
    have heq : ∀ᶠ z in 𝓝 (0 : ℂ), (FormalMultilinearSeries.ofScalars ℂ G).sum z =
        (FormalMultilinearSeries.ofScalars ℂ Gc).sum z := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
      rw [Metric.mem_ball, dist_zero_right] at hz
      have hGz : (FormalMultilinearSeries.ofScalars ℂ G).sum z = 1 := by
        change FormalMultilinearSeries.ofScalarsSum G z = 1
        rw [FormalMultilinearSeries.ofScalars_sum_eq]
        simpa only [smul_eq_mul] using (hB z hz).tsum_eq
      have hGcz : (FormalMultilinearSeries.ofScalars ℂ Gc).sum z = 1 := by
        change FormalMultilinearSeries.ofScalarsSum Gc z = 1
        rw [FormalMultilinearSeries.ofScalars_sum_eq]
        simp [hGc]
      rw [hGz, hGcz]
    have hser := h1.eq_formalMultilinearSeries_of_eventually h2 heq
    have hfun : G = Gc := FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ hser
    intro n
    exact congrFun hfun n
  ext n
  simpa [hG] using hC n

private theorem exists_re_lt_and_cpow_neg_eq {N : ℝ} (hN : 1 < N) (σ : ℝ) {X : ℂ} (hX : X ≠ 0)
    (hXr : ‖X‖ < N ^ (-σ)) : ∃ s : ℂ, σ < s.re ∧ ((N : ℂ) ^ (-s)) = X := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  refine ⟨-(Complex.log X / (Real.log N : ℂ)), ?_, ?_⟩
  · have hre : (-(Complex.log X / (Real.log N : ℂ))).re = -(Real.log ‖X‖ / Real.log N) := by
      rw [Complex.neg_re, Complex.div_ofReal_re, Complex.log_re]
    rw [hre]
    have hlt : Real.log ‖X‖ < -σ * Real.log N := by
      have := Real.log_lt_log (norm_pos_iff.mpr hX) hXr
      rwa [Real.log_rpow hN0] at this
    have hdiv : Real.log ‖X‖ / Real.log N < -σ := (div_lt_iff₀ hlogN).mpr hlt
    linarith
  · have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    rw [Complex.cpow_def_of_ne_zero hNc, neg_neg, ← Complex.ofReal_log hN0.le]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hlogN.ne')]
    exact Complex.exp_log hX

private theorem hasSum_cone_coeff_mul_pow (c : ℤ × ℤ → ℂ) (hc : ∀ p : ℤ × ℤ, ¬ (0 ≤ p.2 ∧ p.2 ≤ p.1) → c p = 0)
    (X S : ℂ) (h : HasSum (fun p : ℤ × ℤ => c p * X ^ (p.1 + p.2).toNat) S) :
    HasSum (fun n : ℕ => (∑ k ∈ Finset.range (n / 2 + 1), c ((n : ℤ) - k, (k : ℤ))) * X ^ n) S := by

  let e : (Σ n : ℕ, Fin (n / 2 + 1)) → ℤ × ℤ := fun q => ((q.1 : ℤ) - (q.2 : ℕ), ((q.2 : ℕ) : ℤ))
  have he : Function.Injective e := by
    rintro ⟨n, k⟩ ⟨n', k'⟩ hq
    simp only [e, Prod.mk.injEq] at hq
    have h1 : (k : ℕ) = k' := by exact_mod_cast hq.2
    have h2 : n = n' := by omega
    subst h2
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Fin.ext h1
  have hrange : ∀ p : ℤ × ℤ, p ∉ Set.range e → c p * X ^ (p.1 + p.2).toNat = 0 := by
    intro p hp
    rw [hc p, zero_mul]
    rintro ⟨h0, h12⟩
    apply hp
    refine ⟨⟨(p.1 + p.2).toNat, ⟨p.2.toNat, ?_⟩⟩, ?_⟩
    · omega
    · ext <;> simp only [e] <;> omega
  have hsig : HasSum (fun q => c (e q) * X ^ ((e q).1 + (e q).2).toNat) S :=
    (he.hasSum_iff hrange).mpr h
  have hdeg : ∀ q : (Σ n : ℕ, Fin (n / 2 + 1)), ((e q).1 + (e q).2).toNat = q.1 := by
    rintro ⟨n, k⟩
    simp only [e]
    omega
  simp_rw [hdeg] at hsig
  refine hsig.sigma fun n => ?_
  rw [Finset.sum_mul, ← Fin.sum_univ_eq_sum_range (fun k => c ((n : ℤ) - k, (k : ℤ)) * X ^ n)]
  exact hasSum_fintype _

end FormalInverse

section EulerEval

private theorem eval_rsEulerPoly_add_mul_eq_mul (a₁ a₂ e₁ e₂ e₃ z : ℂ) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly (a₁ + a₂) (a₁ * a₂) e₁ e₂ e₃).eval z =
      (1 - e₁ * (a₁ * z) + e₂ * (a₁ * z) ^ 2 - e₃ * (a₁ * z) ^ 3) *
        (1 - e₁ * (a₂ * z) + e₂ * (a₂ * z) ^ 2 - e₃ * (a₂ * z) ^ 3) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

end EulerEval

section Algebraic

namespace SphericalValuesAssembly

open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg UnramifiedWhittaker

private theorem eq_of_right_inverses {R : Type*} [CommRing R] {x y e : R} (hx : x * e = 1)
    (hy : y * e = 1) : x = y := by
  calc x = x * (y * e) := by rw [hy, mul_one]
    _ = y * (x * e) := by ring
    _ = y := by rw [hx, mul_one]

private def valueMinors (h : ℕ → ℂ) (k₁ k₂ : ℕ) : ℂ :=
  if k₂ = 0 then h k₁ else h k₁ * h k₂ - h (k₁ + 1) * h (k₂ - 1)

private theorem valueMinors_zero (h : ℕ → ℂ) (k : ℕ) : valueMinors h k 0 = h k := by
  simp [valueMinors]

private theorem valueMinors_succ (h : ℕ → ℂ) (k₁ k₂ : ℕ) :
    valueMinors h k₁ (k₂ + 1) = h k₁ * h (k₂ + 1) - h (k₁ + 1) * h k₂ := by
  simp [valueMinors]

private theorem mk_valueMinors_mul_eq_one (e₁ e₂ e₃ a₁ a₂ : ℂ) :
    PowerSeries.mk (fun n : ℕ => ∑ k ∈ Finset.range (n / 2 + 1),
        (a₁ * a₂) ^ k * heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) (n - 2 * k) *
          valueMinors (sphericalTorusValue e₁ e₂ e₃) (n - k) k) *
      ↑(rsEulerPoly (a₁ + a₂) (a₁ * a₂) e₁ e₂ e₃) = (1 : PowerSeries ℂ) :=
  mk_twoRowCauchySum_mul_coe_rsEulerPoly_eq_one (a₁ + a₂) (a₁ * a₂) e₁ e₂ e₃
    (heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂)) (by simp [heckeRecursionSeq]) (by simp [heckeRecursionSeq])
    (fun m => by simp [heckeRecursionSeq]) (sphericalTorusValue e₁ e₂ e₃) rfl rfl rfl (fun n => rfl)
    (valueMinors (sphericalTorusValue e₁ e₂ e₃)) (valueMinors_zero _) (valueMinors_succ _)

private theorem eq_sphericalTorusValue_of_forall_mk_mul_eq_one (e₁ e₂ e₃ : ℂ) (V : ℕ → ℕ → ℂ)
    (hV : ∀ a₁ a₂ : ℂ, a₁ * a₂ ≠ 0 →
      PowerSeries.mk (fun n : ℕ => ∑ k ∈ Finset.range (n / 2 + 1),
          (a₁ * a₂) ^ k * heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) (n - 2 * k) * V (n - k) k) *
        ↑(rsEulerPoly (a₁ + a₂) (a₁ * a₂) e₁ e₂ e₃) = (1 : PowerSeries ℂ)) :
    (∀ k : ℕ, V k 0 = sphericalTorusValue e₁ e₂ e₃ k) ∧
      ∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ →
        V k₁ (k₂ + 1) =
          sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
            sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂ := by
  have key : ∀ n k : ℕ, k ≤ n / 2 → V (n - k) k = valueMinors (sphericalTorusValue e₁ e₂ e₃) (n - k) k := by
    intro n k hk
    have hz := eq_zero_of_forall_sum_mul_pow_mul_heckeRecursionSeq_eq_zero n
      (fun j => V (n - j) j - valueMinors (sphericalTorusValue e₁ e₂ e₃) (n - j) j) ?_ k hk
    · exact sub_eq_zero.1 hz
    intro a₁ a₂ ha
    have hcoeff := congrArg (PowerSeries.coeff n)
      (eq_of_right_inverses (hV a₁ a₂ ha) (mk_valueMinors_mul_eq_one e₁ e₂ e₃ a₁ a₂))
    simp only [PowerSeries.coeff_mk] at hcoeff
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hcoeff
    rw [← hcoeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨fun k => ?_, fun k₁ k₂ hle => ?_⟩
  · have hk := key k 0 (Nat.zero_le _)
    rwa [Nat.sub_zero, valueMinors_zero] at hk
  · have hk : k₂ + 1 ≤ (k₁ + k₂ + 1) / 2 := by omega
    have h := key (k₁ + k₂ + 1) (k₂ + 1) hk
    have hidx : k₁ + k₂ + 1 - (k₂ + 1) = k₁ := by omega
    rwa [hidx, valueMinors_succ] at h

end SphericalValuesAssembly

end Algebraic

section CellMass

section CosetCell

variable {G : Type*} [Group G]

open scoped Pointwise in

private theorem cosetCell_eq_mul (H K : Subgroup G) :
    {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} = (H : Set G) * (K : Set G) := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨n, hn, k, hk, rfl⟩; exact ⟨n, hn, k, hk, rfl⟩
  · rintro ⟨n, hn, k, hk, rfl⟩; exact ⟨n, hn, k, hk, rfl⟩

open scoped Pointwise in
private theorem cosetCell_isOpen [TopologicalSpace G] [ContinuousMul G] (H K : Subgroup G)
    (hK : IsOpen (K : Set G)) :
    IsOpen {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} := by
  rw [cosetCell_eq_mul]; exact hK.mul_left

private theorem mem_cosetCell_mul_iff (H K : Subgroup G) {h : G} (hh : h ∈ H) (g : G) :
    h * g ∈ {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} ↔ g ∈ {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} := by
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, k, hk, e⟩
    exact ⟨h⁻¹ * n, H.mul_mem (H.inv_mem hh) hn, k, hk, by rw [mul_assoc, ← e, inv_mul_cancel_left]⟩
  · rintro ⟨n, hn, k, hk, rfl⟩
    exact ⟨h * n, H.mul_mem hh hn, k, hk, (mul_assoc _ _ _).symm⟩

private theorem preimage_out_mem_cosetCell (H K : Subgroup G) :
    (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) ⁻¹'
        {q : MulAction.orbitRel.Quotient H G | q.out ∈ {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k}} =
      {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq]

  have horb : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ∈ MulAction.orbit H g :=
    MulAction.orbitRel_apply.1 (Quotient.mk_out' g)
  obtain ⟨h, hhg⟩ := MulAction.mem_orbit_iff.1 horb
  have e : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = (h : G) * g := by
    rw [← hhg]; rfl
  rw [e]
  exact mem_cosetCell_mul_iff H K h.2 g

end CosetCell

section Mass

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private theorem measure_eq_mul_withDensity_cosetCell (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant]
    [MeasureTheory.SFinite μ] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : MeasureTheory.Measure H)
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G)) :
    μ (K : Set G) =
      μH (Subtype.val ⁻¹' (K : Set G)) *
        (μ.withDensity (HaarQuotient.density H μH)) {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} := by
  set cell : Set G := {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} with hcell
  set Sq : Set (MulAction.orbitRel.Quotient H G) := {q | q.out ∈ cell} with hSq
  have hcell_open : IsOpen cell := cosetCell_isOpen H K hKo
  have hpre : (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) ⁻¹' Sq = cell :=
    preimage_out_mem_cosetCell H K
  have hSq_meas : MeasurableSet Sq := by
    rw [measurableSet_quotient, hpre]; exact hcell_open.measurableSet
  have hKH_meas : MeasurableSet (Subtype.val ⁻¹' (K : Set G) : Set H) :=
    (hKo.preimage continuous_subtype_val).measurableSet

  have hf : Measurable ((K : Set G).indicator fun _ => (1 : ENNReal)) :=
    measurable_const.indicator hKo.measurableSet
  have hformula := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH
    ((K : Set G).indicator fun _ => (1 : ENNReal)) hf
  rw [MeasureTheory.lintegral_indicator_const hKo.measurableSet, one_mul] at hformula

  have hinner : ∀ q : MulAction.orbitRel.Quotient H G,
      ∫⁻ x : H, (K : Set G).indicator (fun _ => (1 : ENNReal)) ((x : G) * q.out) ∂μH =
        Sq.indicator (fun _ => μH (Subtype.val ⁻¹' (K : Set G))) q := by
    intro q
    by_cases hq : q ∈ Sq
    · rw [Set.indicator_of_mem hq]
      obtain ⟨n, hn, k, hk, hout⟩ := hq
      have hpt : ∀ x : H, (K : Set G).indicator (fun _ => (1 : ENNReal)) ((x : G) * q.out) =
          (Subtype.val ⁻¹' (K : Set G) : Set H).indicator (fun _ => (1 : ENNReal)) (x * ⟨n, hn⟩) := by
        intro x
        have h1 : (x : G) * q.out ∈ (K : Set G) ↔ (x * ⟨n, hn⟩ : H) ∈ (Subtype.val ⁻¹' (K : Set G) : Set H) := by
          rw [Set.mem_preimage, hout, ← mul_assoc, Subgroup.coe_mul]
          exact K.mul_mem_cancel_right hk
        by_cases hm : (x : G) * q.out ∈ (K : Set G)
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (h1.1 hm)]
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (h1.2 h))]
      simp_rw [hpt]
      rw [MeasureTheory.lintegral_mul_right_eq_self
        (fun y : H => (Subtype.val ⁻¹' (K : Set G) : Set H).indicator (fun _ => (1 : ENNReal)) y) (⟨n, hn⟩ : H),
        MeasureTheory.lintegral_indicator_const hKH_meas, one_mul]
    · rw [Set.indicator_of_notMem hq]
      have hzero : ∀ x : H, (K : Set G).indicator (fun _ => (1 : ENNReal)) ((x : G) * q.out) = 0 := by
        intro x
        apply Set.indicator_of_notMem
        intro hmem
        apply hq

        show q.out ∈ cell
        have : (x : G) * q.out ∈ cell := ⟨1, H.one_mem, (x : G) * q.out, hmem, (one_mul _).symm⟩
        exact (mem_cosetCell_mul_iff H K x.2 q.out).1 this
      simp_rw [hzero]
      exact MeasureTheory.lintegral_zero
  simp_rw [hinner] at hformula
  rw [MeasureTheory.lintegral_indicator_const hSq_meas, HaarQuotient.measure,
    MeasureTheory.Measure.map_apply measurable_quotient_mk'' hSq_meas, hpre] at hformula
  exact hformula

private theorem withDensity_density_cosetCell_ne_zero_and_ne_top (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : MeasureTheory.Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    (μ.withDensity (HaarQuotient.density H μH)) {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} ≠ 0 ∧
      (μ.withDensity (HaarQuotient.density H μH)) {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} ≠ ⊤ := by
  have hμK := measure_eq_mul_withDensity_cosetCell μ H hH μH K hKo

  have hK0 : μ (K : Set G) ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hKtop : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne

  have hc0 : μH (Subtype.val ⁻¹' (K : Set G)) ≠ 0 :=
    ((hKo.preimage continuous_subtype_val).measure_pos μH ⟨1, K.one_mem⟩).ne'
  constructor
  · intro h0
    rw [h0, mul_zero] at hμK
    exact hK0 hμK
  · intro htop
    rw [htop, ENNReal.mul_top hc0] at hμK
    exact hKtop hμK

private theorem toReal_withDensity_density_cosetCell_ne_zero (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : MeasureTheory.Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    ((((μ.withDensity (HaarQuotient.density H μH)) {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k}).toReal : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨h0, htop⟩ := withDensity_density_cosetCell_ne_zero_and_ne_top μ H hH μH K hKo hKc
  exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩

end Mass

end CellMass

section CellLemmas

namespace SphericalCellLemmas

section TorusPoints

variable {F : Type*} [Field F]

private theorem scalarPi_zpow_coe (π : F) (hπ : π ≠ 0) (n : ℤ) :
    ((UnramifiedWhittaker.scalarPi π hπ ^ n : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![π ^ n, 0; 0, π ^ n] := by
  have hs : ((UnramifiedWhittaker.scalarPi π hπ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![π, 0; 0, π] := rfl
  have hsi : (((UnramifiedWhittaker.scalarPi π hπ)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![π⁻¹, 0; 0, π⁻¹] := by
    rw [Matrix.coe_units_inv, hs]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hπ]
  induction n using Int.induction_on with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih, hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, zpow_add_one₀ hπ]
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih, hsi]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, zpow_sub_one₀ hπ]

private theorem diagZ_mul_scalarPi_zpow_coe (π : F) (hπ : π ≠ 0) (m n : ℤ) :
    ((UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![π ^ m * π ^ n, 0; 0, π ^ n] := by
  have hd : ((UnramifiedWhittaker.diagZ π hπ m : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![π ^ m, 0; 0, 1] :=
    rfl
  rw [Units.val_mul, hd, scalarPi_zpow_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem iotaGL_diagZ_mul_scalarPi_zpow_coe (π : F) (hπ : π ≠ 0) (m n : ℤ) :
    ((LanglandsTunnell.CubicInduction.iotaGL
        (UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![π ^ (m + n), π ^ n, 1] := by
  rw [LanglandsTunnell.CubicInduction.coe_iotaGL, diagZ_mul_scalarPi_zpow_coe, zpow_add₀ hπ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.embedMat2, Matrix.diagonal]

end TorusPoints

section Local

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

private theorem psiLocal_eq_one_of_valued_le_one (x : v.adicCompletion ℚ) (hx : Valued.v x ≤ 1) :
    NumberField.StandardAddChar.psiLocal ℚ v x = 1 :=
  LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v x
    ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers ℚ) ℚ v).2 hx)

private theorem exists_valued_le_one_and_psiLocal_inv_ne_one :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧
      (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ ((LanglandsTunnell.CubicInduction.varpi v)⁻¹ * x) ≠ 1 := by
  have hψk : ∃ k : ℤ, ∀ x : v.adicCompletion ℚ,
      Valued.v x ≤ WithZero.exp k → NumberField.StandardAddChar.psiLocal ℚ v x = 1 :=
    ⟨0, fun x hx => psiLocal_eq_one_of_valued_le_one v x (by rwa [WithZero.exp_zero] at hx)⟩
  obtain ⟨x₁, hx₁, hψx₁⟩ :=
    (LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v
      (NumberField.StandardAddChar.psiLocal ℚ v) hψk (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v)).2
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat v, zero_add] at hx₁
  refine ⟨LanglandsTunnell.CubicInduction.varpi v * x₁, ?_, ?_⟩
  · rw [map_mul, NumberField.AdelicLevel.valued_uniformizerUnit ℚ v]
    calc WithZero.exp (-1 : ℤ) * Valued.v x₁ ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (1 : ℤ) :=
          mul_le_mul_right hx₁ _
      _ = 1 := by rw [← WithZero.exp_add]; norm_num
  · rw [inv_mul_cancel_left₀ (LanglandsTunnell.CubicInduction.varpi_ne_zero v), AddChar.inv_apply']
    exact inv_ne_one.2 hψx₁

private theorem valued_zpow_eq_exp_neg {π : v.adicCompletion ℚ} (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (π ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, show k * (-1 : ℤ) = -k by ring]

private theorem valued_lt_of_neg_or_neg {π : v.adicCompletion ℚ} (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
    {m n : ℤ} (h : m < 0 ∨ n < 0) :
    Valued.v ((![π ^ (m + n), π ^ n, 1] : Fin 3 → v.adicCompletion ℚ) 1) <
        Valued.v ((![π ^ (m + n), π ^ n, 1] : Fin 3 → v.adicCompletion ℚ) 0) ∨
      Valued.v ((![π ^ (m + n), π ^ n, 1] : Fin 3 → v.adicCompletion ℚ) 2) <
        Valued.v ((![π ^ (m + n), π ^ n, 1] : Fin 3 → v.adicCompletion ℚ) 1) := by
  show Valued.v (π ^ n) < Valued.v (π ^ (m + n)) ∨ Valued.v (1 : v.adicCompletion ℚ) < Valued.v (π ^ n)
  have h1 : Valued.v (1 : v.adicCompletion ℚ) = WithZero.exp (0 : ℤ) := by rw [map_one, WithZero.exp_zero]
  rw [valued_zpow_eq_exp_neg v hϖ, valued_zpow_eq_exp_neg v hϖ, h1]
  rcases h with hm | hn
  · exact Or.inl (WithZero.exp_lt_exp.2 (by omega))
  · exact Or.inr (WithZero.exp_lt_exp.2 (by omega))

private theorem modulus_det_diagZ_mul_scalarPi_zpow {π : v.adicCompletion ℚ} (hπ : π ≠ 0)
    (hnorm : ‖π‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) (m n : ℤ) :
    (LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det (UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n) :
          (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(m + 2 * n)) := by
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    intro h0
    have hπ' : ‖π‖ ≠ 0 := norm_ne_zero_iff.2 hπ
    rw [hnorm, h0, inv_zero] at hπ'
    exact hπ' rfl
  have hdet : ((Matrix.GeneralLinearGroup.det
      (UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n) : (v.adicCompletion ℚ)ˣ) :
        v.adicCompletion ℚ) =
      Matrix.det ((UnramifiedWhittaker.diagZ π hπ m * UnramifiedWhittaker.scalarPi π hπ ^ n :
        GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := rfl
  rw [hdet, diagZ_mul_scalarPi_zpow_coe, Matrix.det_fin_two_of, mul_zero, sub_zero,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v, coe_nnnorm]
  simp only [norm_mul, norm_zpow, hnorm, inv_zpow']
  rw [← zpow_add₀ hN, ← zpow_add₀ hN]
  congr 1
  ring

end Local

end SphericalCellLemmas

end CellLemmas

section UniformiserNormScale

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace SphericalValuesLemmas

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem absNorm_span_intCast_eq (z : ℤ) : Ideal.absNorm (Ideal.span {(z : 𝓞 ℚ)}) = z.natAbs := by
  rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)) z, Algebra.norm_algebraMap,
    RingOfIntegers.rank, Module.finrank_self, pow_one]

private theorem absNorm_span_natCast_eq (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  simpa using absNorm_span_intCast_eq (n : ℤ)

private theorem valued_natCast_eq_intValuation (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = v.intValuation (n : 𝓞 ℚ) := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n, ← map_natCast (algebraMap (𝓞 ℚ) ℚ) n]
  exact AdelicLevel.valued_algebraMap v (n : 𝓞 ℚ)

private theorem intValuation_natCast_absNorm :
    v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := by
  have hN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have h1 : v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_mem, pow_one]
    exact hmem
  have h2 : ¬ v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_mem]
    intro hmem2
    have hle : Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal ^ 2 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hmem2
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, absNorm_span_natCast_eq] at hdvd
    have hle' := Nat.le_of_dvd (by omega) hdvd
    nlinarith
  have hr : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) = WithZero.exp (-(c : ℤ)) :=
    ⟨_, v.intValuation_if_neg hr⟩
  rw [hc, WithZero.exp_le_exp] at h1 h2
  rw [hc]
  congr 1
  omega

private theorem valued_ratPrimeAt_eq_exp_neg_one :
    Valued.v (LanglandsTunnell.CubicInduction.ratPrimeAt v) = WithZero.exp (-1 : ℤ) := by
  show Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) = _
  rw [valued_natCast_eq_intValuation, intValuation_natCast_absNorm]

private theorem norm_ratPrimeAt_eq_inv :
    ‖LanglandsTunnell.CubicInduction.ratPrimeAt v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [FinitePlace.norm_def, valued_ratPrimeAt_eq_exp_neg_one, WithZero.exp_eq_coe_ofAdd,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd, zpow_neg_one]
  simp

private theorem heckeRecursionSeq_div_eq (N lam om : ℂ) (hN : N ≠ 0) (m : ℕ) :
    UnramifiedWhittaker.heckeRecursionSeq N lam (om / N) m =
      (N ^ m)⁻¹ * UnramifiedWhittaker.heckeRecursionSeq 1 lam om m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [UnramifiedWhittaker.heckeRecursionSeq]
  | one => simp [UnramifiedWhittaker.heckeRecursionSeq, div_eq_inv_mul]
  | more m ih0 ih1 =>
    simp only [UnramifiedWhittaker.heckeRecursionSeq, ih0, ih1, pow_succ]
    field_simp

end SphericalValuesLemmas

end UniformiserNormScale

section Instances

open IsDedekindDomain NumberField MeasureTheory

namespace CellInstances

section Generic

private theorem secondCountableTopology_GL2_of_ring (A : Type*) [Ring A] [TopologicalSpace A]
    [SecondCountableTopology A] : SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin 2) (Fin 2) A)).isInducing.secondCountableTopology

private theorem isMulRightInvariant_of_comm {H : Type*} [Group H] [MeasurableSpace H] (μ : Measure H)
    [μ.IsMulLeftInvariant] (hcomm : ∀ a b : H, a * b = b * a) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun h : H => h * g) = fun h : H => g * h := funext fun h => hcomm h g
  simp only [this]
  exact map_mul_left_eq_self μ g

end Generic

section Unipotent

variable {R : Type*} [CommRing R]

private theorem coe_range_unipotentGL2Hom :
    ((AutomorphicForm.unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) =
      {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [AutomorphicForm.unipotentGL2Hom]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) R) 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.unipotentGL2Hom, h00, h10, h11]

private theorem isClosed_range_unipotentGL2Hom [TopologicalSpace R] [T2Space R] :
    IsClosed ((AutomorphicForm.unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) := by
  rw [coe_range_unipotentGL2Hom]
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  exact (isClosed_eq (hc 0 0) continuous_const).inter
    ((isClosed_eq (hc 1 0) continuous_const).inter (isClosed_eq (hc 1 1) continuous_const))

private theorem mul_comm_range_unipotentGL2Hom (a b : (AutomorphicForm.unipotentGL2Hom (R := R)).range) :
    a * b = b * a := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

end Unipotent

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_localLevelOne_top :
    (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))) =
      AutomorphicForm.localIntegralSet ℚ v := by
  ext g
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff, AutomorphicForm.mem_localIntegralSet]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.integral, h₂.integral⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁, ?_, ?_⟩, ⟨h₂, ?_, ?_⟩⟩ <;> rw [AdelicLevel.idealBound_top]
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (h₁ 1 0)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (sub_mem (h₁ 1 1) (one_mem _))
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (h₂ 1 0)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (sub_mem (h₂ 1 1) (one_mem _))

private theorem isOpen_localLevelOne_top :
    IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  rw [coe_localLevelOne_top]
  exact AutomorphicForm.isOpen_localIntegralSet ℚ v

private theorem isCompact_localLevelOne_top :
    IsCompact (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  rw [coe_localLevelOne_top]
  exact AutomorphicForm.isCompact_localIntegralSet ℚ v

private theorem secondCountableTopology_adicCompletion : SecondCountableTopology (v.adicCompletion ℚ) := by
  haveI : Countable (WithVal (v.valuation ℚ)) := (WithVal.equiv (v := v.valuation ℚ)).injective.countable
  infer_instance

private theorem secondCountableTopology_GL2 : SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ)) := by
  haveI := secondCountableTopology_adicCompletion v
  exact secondCountableTopology_GL2_of_ring _

end Local

end CellInstances

end Instances

section ModulusLemmas

open IsDedekindDomain NumberField

namespace CellModulus

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_det_eq_one_of_mem (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  have hk' : k ∈ AutomorphicForm.localIntegralSet ℚ v := by
    rw [← CellInstances.coe_localLevelOne_top v]
    exact hk
  obtain ⟨h₁, h₂⟩ := (AutomorphicForm.mem_localIntegralSet ℚ v).1 hk'
  have hdet : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) →
      Valued.v ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 := by
    intro g hg
    change Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ≤ 1
    rw [Matrix.det_fin_two]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1
      (sub_mem (mul_mem (hg 0 0) (hg 1 1)) (mul_mem (hg 0 1) (hg 1 0)))
  have hle : Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 :=
    hdet k h₁
  have hinv : Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 :=
    hdet k⁻¹ h₂
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at hinv
  have hne : Valued.v ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
  exact le_antisymm hle ((inv_le_one₀ (pos_iff_ne_zero.2 hne)).1 hinv)

private theorem nnnorm_det_eq_one_of_mem (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    ‖((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖₊ = 1 := by
  ext
  rw [coe_nnnorm, FinitePlace.norm_def, valued_det_eq_one_of_mem v k hk, map_one, NNReal.coe_one]

private theorem modulus_det_mul_of_mem (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det (g * k) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) : ℝ) =
      ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) : ℝ) := by
  rw [map_mul, Units.val_mul, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, nnnorm_mul, nnnorm_det_eq_one_of_mem v k hk,
    mul_one]

private theorem modulus_det_unipotent_mul (n : GL (Fin 2) (v.adicCompletion ℚ))
    (hn : n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det (n * g) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) : ℝ) =
      ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) : ℝ) := by
  obtain ⟨x, rfl⟩ := hn
  have hdet : Matrix.GeneralLinearGroup.det (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ) x) = 1 := by
    ext
    show Matrix.det ((AutomorphicForm.unipotentGL2 x.toAdd : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1
    rw [AutomorphicForm.unipotentGL2_coe, Matrix.det_fin_two_of]
    ring
  rw [map_mul, hdet, one_mul]

private theorem unipotentGL2Hom_eq_unipotent (x : Multiplicative (v.adicCompletion ℚ)) :
    AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ) x = UnramifiedWhittaker.unipotent x.toAdd :=
  Units.ext rfl

end CellModulus

end ModulusLemmas

section Cpow

namespace SphericalValuesLemmas

private theorem ofReal_zpow_neg_cpow {N : ℝ} (hN : 0 < N) (k : ℕ) (w : ℂ) :
    (((N ^ (-(k : ℤ)) : ℝ) : ℂ)) ^ w = ((N : ℂ) ^ (-w)) ^ k := by
  have h1 : (N ^ (-(k : ℤ)) : ℝ) = N ^ (-(k : ℝ)) := by
    rw [show (-(k : ℝ)) = ((-(k : ℤ) : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
  rw [h1, ← Complex.cpow_mul_ofReal_nonneg hN.le, ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

end SphericalValuesLemmas

end Cpow

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker

namespace SphericalValuesAnalytic

open SphericalValuesAssembly SphericalValuesLemmas CellInstances CellModulus SphericalCellLemmas

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem apply_mul_scalarPi_pow {π : v.adicCompletion ℚ} (hπ : π ≠ 0)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (z : ℂ)
    (hZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W₂ (g * scalarPi π hπ) = z * W₂ g)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    ∀ n : ℕ, W₂ (g * scalarPi π hπ ^ n) = z ^ n * W₂ g
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, ← mul_assoc, hZ, apply_mul_scalarPi_pow hπ W₂ z hZ g n, pow_succ]
    ring

private theorem apply_iotaGL_mul_mul_apply_of_mem_range (W : LocalGL3 v → ℂ)
    (hψ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (n : GL (Fin 2) (v.adicCompletion ℚ)) (hn : n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    W (iotaGL (n * g)) * W₂ (n * g) = W (iotaGL g) * W₂ g := by
  obtain ⟨x, rfl⟩ := hn
  have h1 : W (iotaGL (unipotentGL2Hom (R := v.adicCompletion ℚ) x * g)) =
      (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x.toAdd * W (iotaGL g) := by
    have h := hψ x.toAdd 0 0 (iotaGL g)
    rw [add_zero] at h
    rw [map_mul, show iotaGL (unipotentGL2Hom (R := v.adicCompletion ℚ) x) = upperUnipotent3 x.toAdd 0 0 from
      iotaGL_unipotentGL2 x.toAdd, h]
  rw [h1, unipotentGL2Hom_eq_unipotent, hW₂ψ, AddChar.inv_apply']
  have hx : NumberField.StandardAddChar.psiLocal ℚ v x.toAdd ≠ 0 := (AddChar.val_isUnit _ _).ne_zero
  field_simp

private theorem apply_iotaGL_mul_mul_apply_of_mem (c : ℕ) (W : LocalGL3 v → ℂ)
    (hW : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g, W (g * k) = W g)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
    (k : GL (Fin 2) (v.adicCompletion ℚ)) (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    W (iotaGL (g * k)) * W₂ (g * k) = W (iotaGL g) * W₂ g := by
  have hk3 : iotaGL k ∈ congruenceK1 (𝓞 ℚ) ℚ v c :=
    (iotaGL_mem_congruenceK1_iff (𝓞 ℚ) ℚ v c k).2 (iotaGL_mem_localMaximalCompact3_of_mem_localLevelOne v hk)
  rw [map_mul, hW _ hk3, hW₂K k g hk]

private theorem iotaGL_diagZ_mul_scalarPi_pow_eq_twoRowPointLocal (k₁ k₂ : ℕ) :
    iotaGL (diagZ (ratPrimeAt v) (ratPrimeAt_ne_zero v) ((k₁ : ℤ) - k₂) *
        scalarPi (ratPrimeAt v) (ratPrimeAt_ne_zero v) ^ ((k₂ : ℕ) : ℤ)) =
      twoRowPointLocal v k₁ k₂ := by
  unfold twoRowPointLocal
  congr 1
  ext i j
  rw [diagZ_mul_scalarPi_zpow_coe, ← zpow_add₀ (ratPrimeAt_ne_zero v), sub_add_cancel]
  have hcoe : ((diagUnits2 (ratPrimeUnit v ^ k₁) (ratPrimeUnit v ^ k₂) : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![ratPrimeAt v ^ k₁, 0; 0, ratPrimeAt v ^ k₂] := by
    simp [coe_diagUnits2, ratPrimeUnit, Units.val_pow_eq_pow_val]
  rw [hcoe, zpow_natCast, zpow_natCast]

private theorem one_lt_absNorm_real : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

end SphericalValuesAnalytic

namespace SphericalValuesAnalytic

open SphericalValuesAssembly SphericalValuesLemmas CellInstances CellModulus SphericalCellLemmas

private theorem forall_mk_mul_eq_one
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K ≤ 3) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (c : ℕ) (W : LocalGL3 v → ℂ) (hψ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    (hW : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g, W (g * k) = W g) (hW1 : W 1 = 1)
    (hid : ∀ {ϖ : v.adicCompletionIntegers ℚ}
      (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) →
      ∀ (a₁ a₂ : ℂ) (_ : a₁ * a₂ ≠ 0)
      (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (_ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
      (_ : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
      (_ : W₂ 1 = 1)
      (_ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
          a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
      (_ : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
        torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m),
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∃ σ₂ : ℝ,
        (∀ s : ℂ, σ₂ < s.re →
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * W₂ g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W (iotaGL g)) W₂ *
              (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                  2))) *
              (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                  2))) =
            (((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
                {g : GL (Fin 2) (v.adicCompletion ℚ) |
                  ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ)))
    (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) :
    PowerSeries.mk (fun n : ℕ => ∑ k ∈ Finset.range (n / 2 + 1),
        (a₁ * a₂) ^ k * heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) (n - 2 * k) *
          ((Ideal.absNorm v.asIdeal : ℂ) ^ (n - k) * W (twoRowPointLocal v (n - k) k))) *
      ↑(rsEulerPoly (a₁ + a₂) (a₁ * a₂) (inducedE1 ℚ (inducedCoeff K μ) v)
          (inducedE2 ℚ (inducedCoeff K μ) v) (inducedE3 ℚ (inducedCoeff K μ) v)) =
        (1 : PowerSeries ℂ) := by

  have hNR : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := one_lt_absNorm_real v
  have hNR0 : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  have hNC : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)

  have hval : Valued.v (ratPrimeAt v) = WithZero.exp (-1 : ℤ) := valued_ratPrimeAt_eq_exp_neg_one v
  have hmem : ratPrimeAt v ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.2 (by norm_num)
  set ϖ₀ : v.adicCompletionIntegers ℚ := ⟨ratPrimeAt v, hmem⟩ with hϖ₀_def
  set π₀ : v.adicCompletion ℚ := algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ₀ with hπ₀_def
  have halg : π₀ = ratPrimeAt v := rfl
  have hπ₀ : π₀ ≠ 0 := by
    rw [halg]
    exact ratPrimeAt_ne_zero v
  have hϖ₀ : Valued.v π₀ = WithZero.exp (-1 : ℤ) := by
    rw [halg]
    exact hval

  have hz : a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := div_ne_zero ha hNC
  obtain ⟨W₂, hW₂ψ, hW₂K, hW₂1, hW₂Z, hW₂T⟩ :=
    exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero v
      (NumberField.StandardAddChar.psiLocal ℚ v) (psiLocal_eq_one_of_valued_le_one v) hπ₀ hϖ₀
      (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) hz (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂)
      (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ))

  letI := localGLBorel ℚ v
  haveI := borelSpace_localGLBorel ℚ v
  haveI : SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ)) := secondCountableTopology_GL2 v
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  set H : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)) := (unipotentGL2Hom (R := v.adicCompletion ℚ)).range
    with hH_def
  have hHc : IsClosed (H : Set (GL (Fin 2) (v.adicCompletion ℚ))) := isClosed_range_unipotentGL2Hom
  haveI : LocallyCompactSpace H := hHc.locallyCompactSpace
  set μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ)) := Measure.haar with hμ₂_def
  set μN : Measure H := Measure.haar with hμN_def
  haveI : μN.IsMulRightInvariant := isMulRightInvariant_of_comm μN mul_comm_range_unipotentGL2Hom
  obtain ⟨σ₂, hint, hident⟩ := hid hπ₀ hϖ₀ a₁ a₂ ha W₂ hW₂ψ hW₂K hW₂1 hW₂Z hW₂T μ₂ μN

  have hvol := toReal_withDensity_density_cosetCell_ne_zero μ₂ H hHc μN (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (isOpen_localLevelOne_top v) (isCompact_localLevelOne_top v)

  set F : ℕ → ℂ := fun n : ℕ => ∑ k ∈ Finset.range (n / 2 + 1),
    (a₁ * a₂) ^ k * heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) (n - 2 * k) *
      ((Ideal.absNorm v.asIdeal : ℂ) ^ (n - k) * W (twoRowPointLocal v (n - k) k)) with hF_def
  set P : Polynomial ℂ := rsEulerPoly (a₁ + a₂) (a₁ * a₂) (inducedE1 ℚ (inducedCoeff K μ) v)
    (inducedE2 ℚ (inducedCoeff K μ) v)
    (inducedE3 ℚ (inducedCoeff K μ) v) with hP_def
  have hPeval : ∀ y : ℂ, P.eval y =
      (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₁ * y) *
        (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₂ * y) := by
    intro y
    rw [hP_def, eval_rsEulerPoly_add_mul_eq_mul, eval_inducedEulerPoly_eq_of_finrank_le_three K hdeg,
      eval_inducedEulerPoly_eq_of_finrank_le_three K hdeg]

  have hF0 : F 0 = 1 := by
    have hpt : twoRowPointLocal v 0 0 = 1 := by
      unfold twoRowPointLocal
      rw [pow_zero, show diagUnits2 (1 : (v.adicCompletion ℚ)ˣ) 1 = 1 from
        Units.ext (by simp [coe_diagUnits2, Matrix.one_fin_two]), map_one]
    simp [hF_def, hpt, hW1, heckeRecursionSeq]

  have hseries : ∀ s : ℂ, σ₂ < s.re →
      HasSum (fun n : ℕ => F n * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) ^ n)
        (((((μ₂.withDensity (HaarQuotient.density H μN))
            {g : GL (Fin 2) (v.adicCompletion ℚ) |
              ∃ n ∈ H, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal :
              ℝ) : ℂ)⁻¹ *
          RSCarrier.rsLocalIntegral μ₂ H μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂) := by
    intro s hs
    set vol : ℂ := ((((μ₂.withDensity (HaarQuotient.density H μN))
        {g : GL (Fin 2) (v.adicCompletion ℚ) |
          ∃ n ∈ H, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal :
          ℝ) : ℂ) with hvol_def
    set X : ℂ := (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2)) with hX_def
    set Y : ℂ := (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s - 1 / 2)) with hY_def
    have hXY : X = ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * Y := by
      rw [hX_def, hY_def, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hNC]
      congr 1
      ring
    have hcell := hasSum_cell_terms_rsLocalIntegral v hπ₀ hϖ₀ μ₂ μN
      (fun g => (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
      (fun n hn g => modulus_det_unipotent_mul v n hn g) (fun k hk g => modulus_det_mul_of_mem v k hk g) s
      (fun g => W (iotaGL g)) W₂ (fun n hn g => apply_iotaGL_mul_mul_apply_of_mem_range v W hψ W₂ hW₂ψ n hn g)
      (fun k hk g => apply_iotaGL_mul_mul_apply_of_mem v c W hW W₂ hW₂K k hk g) (hint s hs)

    set cp : ℤ × ℤ → ℂ := fun p => if 0 ≤ p.2 ∧ p.2 ≤ p.1 then
      vol * ((a₁ * a₂) ^ p.2.toNat * heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) (p.1 - p.2).toNat *
        ((Ideal.absNorm v.asIdeal : ℂ) ^ p.1.toNat * W (twoRowPointLocal v p.1.toNat p.2.toNat))) else 0 with hcp_def
    have hcp0 : ∀ p : ℤ × ℤ, ¬ (0 ≤ p.2 ∧ p.2 ≤ p.1) → cp p = 0 := fun p hp => by simp [hcp_def, hp]
    have hterm : ∀ p : ℤ × ℤ, cp p * X ^ (p.1 + p.2).toNat = vol * ((Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2)) *
        ((W (iotaGL (diagZ π₀ hπ₀ (p.1 - p.2) * scalarPi π₀ hπ₀ ^ p.2)) *
            W₂ (diagZ π₀ hπ₀ (p.1 - p.2) * scalarPi π₀ hπ₀ ^ p.2)) *
          (((modulus ((Matrix.GeneralLinearGroup.det
              (diagZ π₀ hπ₀ (p.1 - p.2) * scalarPi π₀ hπ₀ ^ p.2) :
                (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))) := by
      rintro ⟨p₁, p₂⟩
      by_cases hp : 0 ≤ p₂ ∧ p₂ ≤ p₁
      ·
        obtain ⟨k₁, rfl⟩ : ∃ k₁ : ℕ, p₁ = k₁ := ⟨p₁.toNat, by omega⟩
        obtain ⟨k₂, rfl⟩ : ∃ k₂ : ℕ, p₂ = k₂ := ⟨p₂.toNat, by omega⟩
        have hk : k₂ ≤ k₁ := by omega
        simp only [hcp_def, if_pos hp, Int.toNat_natCast]
        rw [show ((k₁ : ℤ) - k₂).toNat = k₁ - k₂ by omega]
        have hpt : W (iotaGL (diagZ π₀ hπ₀ ((k₁ : ℤ) - k₂) * scalarPi π₀ hπ₀ ^ ((k₂ : ℕ) : ℤ))) =
            W (twoRowPointLocal v k₁ k₂) :=
          congrArg W (iotaGL_diagZ_mul_scalarPi_pow_eq_twoRowPointLocal v k₁ k₂)
        have hW₂pt : W₂ (diagZ π₀ hπ₀ ((k₁ : ℤ) - k₂) * scalarPi π₀ hπ₀ ^ ((k₂ : ℕ) : ℤ)) =
            (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) ^ k₂ *
              (((Ideal.absNorm v.asIdeal : ℂ) ^ (k₁ - k₂))⁻¹ * heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) (k₁ - k₂)) := by
          rw [zpow_natCast, apply_mul_scalarPi_pow v hπ₀ W₂ _ hW₂Z, hW₂T, torusFactor,
            if_pos (by omega : (0 : ℤ) ≤ (k₁ : ℤ) - k₂), show ((k₁ : ℤ) - k₂).toNat = k₁ - k₂ by omega,
            heckeRecursionSeq_div_eq _ _ _ hNC]
        have hδpt : ((modulus ((Matrix.GeneralLinearGroup.det
              (diagZ π₀ hπ₀ ((k₁ : ℤ) - k₂) * scalarPi π₀ hπ₀ ^ ((k₂ : ℕ) : ℤ)) :
                (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) = Y ^ (k₁ + k₂) := by
          rw [modulus_det_diagZ_mul_scalarPi_zpow v hπ₀ (norm_ratPrimeAt_eq_inv v),
            show -(((k₁ : ℤ) - k₂) + 2 * ((k₂ : ℕ) : ℤ)) = -((k₁ + k₂ : ℕ) : ℤ) by push_cast; ring,
            ofReal_zpow_neg_cpow hNR0, hY_def, Complex.ofReal_natCast]
        rw [hpt, hW₂pt, hδpt, show ((k₁ : ℤ) + k₂).toNat = k₁ + k₂ by omega, hXY, mul_pow,
          show ((k₁ : ℤ) - k₂) = ((k₁ - k₂ : ℕ) : ℤ) by omega, zpow_natCast]
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
        subst hj
        rw [Nat.add_sub_cancel_left]
        have hpow : ((Ideal.absNorm v.asIdeal : ℂ) * (Ideal.absNorm v.asIdeal : ℂ)⁻¹) ^ k₂ = 1 := by
          rw [mul_inv_cancel₀ hNC, one_pow]
        simp only [div_eq_mul_inv, mul_pow, ← inv_pow]
        linear_combination (vol * (a₁ * a₂) ^ k₂ * heckeRecursionSeq 1 (a₁ + a₂) (a₁ * a₂) j *
          W (twoRowPointLocal v (k₂ + j) k₂) * Y ^ (k₂ + j + k₂) * (Ideal.absNorm v.asIdeal : ℂ) ^ j *
          ((Ideal.absNorm v.asIdeal : ℂ)⁻¹) ^ j * ((Ideal.absNorm v.asIdeal : ℂ)⁻¹) ^ k₂) * hpow
      ·
        have hzero : W (iotaGL (diagZ π₀ hπ₀ (p₁ - p₂) * scalarPi π₀ hπ₀ ^ p₂)) = 0 :=
          eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn_of_mem_congruenceK1 v _ W c hW hψ
            (exists_valued_le_one_and_psiLocal_inv_ne_one v) _ _
            (iotaGL_diagZ_mul_scalarPi_zpow_coe _ hπ₀ (p₁ - p₂) p₂)
            (valued_lt_of_neg_or_neg v hϖ₀ (by omega))
        rw [hcp0 _ hp, hzero]
        simp
    have hcone := hasSum_cone_coeff_mul_pow cp hcp0 X _ (hcell.congr_fun hterm)
    have hcoeff : ∀ n : ℕ, (∑ k ∈ Finset.range (n / 2 + 1), cp ((n : ℤ) - k, (k : ℤ))) = vol * F n := by
      intro n
      rw [hF_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      have hk' : (0 : ℤ) ≤ (k : ℤ) ∧ (k : ℤ) ≤ (n : ℤ) - k := by constructor <;> omega
      simp only [hcp_def, if_pos hk', Int.toNat_natCast, show ((n : ℤ) - k).toNat = n - k by omega,
        show ((n : ℤ) - k - k).toNat = n - 2 * k by omega]
    simp_rw [hcoeff] at hcone
    have hvol' : vol ≠ 0 := hvol
    refine (hcone.mul_left vol⁻¹).congr_fun fun n => ?_
    field_simp

  refine mk_mul_coe_eq_one_of_forall_tsum_mul_eval_eq_one F P (Real.rpow_pos_of_pos hNR0 (-(σ₂ + 1 / 2))) ?_ ?_
  · intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      exact (hasSum_single (f := fun n : ℕ => F n * (0 : ℂ) ^ n) 0 fun n hn => by simp [hn]).summable
    · obtain ⟨s', hs', hzs⟩ := exists_re_lt_and_cpow_neg_eq hNR (σ₂ + 1 / 2) hz0 hz
      have hs : σ₂ < (s' - 1 / 2).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re] at hs' ⊢
        norm_num at hs' ⊢
        linarith
      have hX : (Ideal.absNorm v.asIdeal : ℂ) ^ (-((s' - 1 / 2) + 1 / 2)) = z := by
        rw [show -((s' - 1 / 2) + 1 / 2) = -s' by ring]
        exact_mod_cast hzs
      have h := hseries (s' - 1 / 2) hs
      rw [hX] at h
      exact h.summable
  · intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      rw [tsum_eq_single 0 (fun n hn => by simp [hn]), hPeval]
      simp [hF0, eval_inducedEulerPoly_eq_of_finrank_le_three K hdeg]
    · obtain ⟨s', hs', hzs⟩ := exists_re_lt_and_cpow_neg_eq hNR (σ₂ + 1 / 2) hz0 hz
      have hs : σ₂ < (s' - 1 / 2).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re] at hs' ⊢
        norm_num at hs' ⊢
        linarith
      have hX : (Ideal.absNorm v.asIdeal : ℂ) ^ (-((s' - 1 / 2) + 1 / 2)) = z := by
        rw [show -((s' - 1 / 2) + 1 / 2) = -s' by ring]
        exact_mod_cast hzs
      have h := hseries (s' - 1 / 2) hs
      rw [hX] at h
      have hid' := hident (s' - 1 / 2) hs
      rw [hX] at hid'
      rw [h.tsum_eq, hPeval, inv_mul_eq_div, div_mul_eq_mul_div, div_eq_one_iff_eq hvol, ← mul_assoc]
      exact hid'

end SphericalValuesAnalytic

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K ≤ 3) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (c : ℕ) (W : LocalGL3 v → ℂ) (hψ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    (hW : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g, W (g * k) = W g) (hW1 : W 1 = 1)
    (hid : ∀ {ϖ : v.adicCompletionIntegers ℚ}
      (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) →
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
        torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m),
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∃ σ₂ : ℝ,
        (∀ s : ℂ, σ₂ < s.re →
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * W₂ g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W (iotaGL g)) W₂ *
              (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                  2))) *
              (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 /
                  2))) =
            (((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
                {g : GL (Fin 2) (v.adicCompletion ℚ) |
                  ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ))) :
    HasSphericalTorusValuesAt (inducedCoeff K μ) v W := by
  have hcN : cNormQ v = (Ideal.absNorm v.asIdeal : ℂ) := rfl
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  have hmain := SphericalValuesAssembly.eq_sphericalTorusValue_of_forall_mk_mul_eq_one
    (inducedE1 ℚ (inducedCoeff K μ) v) (inducedE2 ℚ (inducedCoeff K μ) v) (inducedE3 ℚ (inducedCoeff K μ) v)
    (fun k₁ k₂ : ℕ => (Ideal.absNorm v.asIdeal : ℂ) ^ k₁ * W (twoRowPointLocal v k₁ k₂))
    (fun a₁ a₂ ha => SphericalValuesAnalytic.forall_mk_mul_eq_one K hdeg μ v c W hψ hW hW1 hid a₁ a₂ ha)
  refine ⟨fun n => ?_, fun k₁ k₂ hk => ?_⟩
  · have h := hmain.1 n
    simp only [twoRowPointLocal_zero_right] at h
    rw [hcN, inv_pow, ← h]
    field_simp
  · have h := hmain.2 k₁ k₂ hk
    try simp only at h
    rw [hcN, inv_pow, ← h]
    field_simp

end S_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_inducedCoeff_of_rsLocalIntegral_eq_cellVolume
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_inducedCoeff_of_rsLocalIntegral_eq_cellVolume (solution)
