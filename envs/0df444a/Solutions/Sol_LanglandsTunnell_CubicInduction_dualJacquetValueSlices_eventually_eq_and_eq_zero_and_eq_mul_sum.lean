-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c2eb24b8-b1d3-5d0f-9afb-a44dd20ed350

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

section

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace WeylTranslateZeta
open LanglandsTunnell.TateLocal

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

section Scaling

end Scaling

section MeasureClasses

private theorem selfDualConst_ne_zero :
    ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (StandardAddChar.psiLocal K v) : ℝ) / 2)) ≠ 0 := by
  have hq : (0 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    have h : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h
  exact (NNReal.rpow_pos hq).ne'

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul (Measure.addHaarMeasure (integersPositiveCompacts K v))
    (selfDualConst_ne_zero K v)

private theorem sFinite_selfDualHaarAt :
    letI := localBorel K v
    SFinite (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  infer_instance

private theorem sFinite_mulMeasure_selfDualHaarAt :
    letI := localBorel K v
    SFinite (mulMeasure (selfDualHaarAt K v)) := by
  letI := localBorel K v
  haveI := sFinite_selfDualHaarAt K v
  unfold mulMeasure
  infer_instance

end MeasureClasses

end WeylTranslateZeta
end

section

open Matrix IsDedekindDomain NumberField

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section TransposeInverse

variable {A : Type*} [CommRing A]

private theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change ((((g * h)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ =
    (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ * (((h⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  change ((((1 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = ((1 : GL (Fin 3) A) : Matrix _ _ _)
  rw [inv_one, Units.val_one, Matrix.transpose_one]

private theorem coe_inv_diagUnitGL2 (a : Aˣ) :
    (((diagUnitGL2 a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![((a⁻¹ : Aˣ) : A), 0; 0, 1] :=
  rfl

private theorem transposeInv3_iotaGL_diagUnitGL2 (a : Aˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 a⁻¹) := by
  refine Units.ext ?_
  change ((((iotaGL (diagUnitGL2 a))⁻¹ : GL (Fin 3) A)) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [← map_inv, coe_iotaGL, coe_iotaGL, coe_inv_diagUnitGL2, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

private theorem coe_longWeyl3_mul_transposeInv3_mul_longWeyl3 (a : Aˣ) (x : A) :
    ((longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          longWeyl3 : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : Aˣ) : A) * x), 0, ((a⁻¹ : Aˣ) : A)] := by
  rw [transposeInv3_one, mul_one, transposeInv3_mul, transposeInv3_mul, transposeInv3_iotaGL_diagUnitGL2,
    transposeInv3_lowerUnipotent21, transposeInv3_weylPrime3]
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, longWeyl3_coe, weylPrime3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

end TransposeInverse

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem longWeyl3_eq_antidiagonal3 : (longWeyl3 : LocalGL3 v) = antidiagonal3 v :=
  Units.ext (longWeyl3_coe.trans (antidiagonal3_coe v).symm)

private theorem coe_dualPoint_mul_antidiagonal3 (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    ((longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          antidiagonal3 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x), 0,
        ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] := by
  rw [← longWeyl3_eq_antidiagonal3]
  exact coe_longWeyl3_mul_transposeInv3_mul_longWeyl3 a x

end Local

end WeylTranslateZeta
end

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar
open scoped Topology

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section TorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem exists_invariance_radius (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ r : ℝ, 0 < r ∧ ∀ p q : Fin 3 → v.adicCompletion ℚ, (∀ i, ‖q i - p i‖ ≤ r) → Φ q = Φ p := by
  classical

  have hultra : ∀ a b c : v.adicCompletion ℚ, dist a c ≤ max (dist a b) (dist b c) :=
    fun a b c => IsUltrametricDist.dist_triangle_max a b c
  have hK : IsCompact (tsupport Φ) := hΦc

  have hball : ∀ x : tsupport Φ, ∃ ε : ℝ, 0 < ε ∧ ∀ q, dist q (x : Fin 3 → v.adicCompletion ℚ) < ε → Φ q = Φ x := by
    intro x
    have hopen : IsOpen {q : Fin 3 → v.adicCompletion ℚ | Φ q = Φ x} := hΦl.isOpen_fiber (Φ x)
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen (x : Fin 3 → v.adicCompletion ℚ) rfl
    exact ⟨ε, hε, fun q hq => hsub hq⟩
  choose ε hεpos hε using hball
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover (fun x : tsupport Φ => Metric.ball (x : Fin 3 → v.adicCompletion ℚ) (ε x))
    (fun x => Metric.isOpen_ball) fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hεpos ⟨y, hy⟩)⟩

  obtain ⟨r, hr, hrJ⟩ : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ J, r < ε x := by
    by_cases hJne : J.Nonempty
    · have hinf : 0 < J.inf' hJne ε := (Finset.lt_inf'_iff hJne).mpr fun y _ => hεpos y
      exact ⟨J.inf' hJne ε / 2, half_pos hinf, fun x hx => (half_lt_self hinf).trans_le (Finset.inf'_le ε hx)⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hJne⟩
  refine ⟨r, hr, ?_⟩

  have key : ∀ p q : Fin 3 → v.adicCompletion ℚ, (∀ i, ‖q i - p i‖ ≤ r) → p ∈ tsupport Φ → Φ q = Φ p := by
    intro p q hpq hp
    obtain ⟨x, hxJ, hpx⟩ := Set.mem_iUnion₂.mp (hJ hp)
    have hpx' : dist p (x : Fin 3 → v.adicCompletion ℚ) < ε x := hpx
    have hqx : dist q (x : Fin 3 → v.adicCompletion ℚ) < ε x := by
      rw [dist_pi_lt_iff (hεpos x)] at hpx' ⊢
      intro i
      refine (hultra (q i) (p i) ((x : Fin 3 → v.adicCompletion ℚ) i)).trans_lt (max_lt ?_ (hpx' i))
      rw [dist_eq_norm]
      exact (hpq i).trans_lt (hrJ x hxJ)
    rw [hε x q hqx, hε x p hpx']
  intro p q hpq
  by_cases hp : p ∈ tsupport Φ
  · exact key p q hpq hp
  by_cases hq : q ∈ tsupport Φ
  · refine (key q p (fun i => ?_) hq).symm
    rw [norm_sub_rev]
    exact hpq i
  rw [image_eq_zero_of_notMem_tsupport hp, image_eq_zero_of_notMem_tsupport hq]

private theorem exists_support_radius (hΦc : HasCompactSupport Φ) :
    ∃ R : ℝ, ∀ p : Fin 3 → v.adicCompletion ℚ, Φ p ≠ 0 → ∀ i, ‖p i‖ ≤ R := by
  have hK : IsCompact (tsupport Φ) := hΦc
  choose C hC using fun i : Fin 3 =>
    hK.exists_bound_of_continuousOn
      ((continuous_apply i).continuousOn : ContinuousOn (fun p : Fin 3 → v.adicCompletion ℚ => p i) (tsupport Φ))
  refine ⟨∑ i, max (C i) 0, fun p hp i => ?_⟩
  have hpK : p ∈ tsupport Φ := subset_tsupport Φ hp
  calc ‖p i‖ ≤ C i := hC i p hpK
    _ ≤ max (C i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (C j) 0 :=
        Finset.single_le_sum (f := fun j => max (C j) 0) (fun j _ => le_max_right _ _) (Finset.mem_univ i)

private theorem valued_le_of_norm_le_zpow
    {x : v.adicCompletion ℚ} {n : ℤ} (hx : ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n) :
    Valued.v x ≤ WithZero.exp n := by
  have hexp : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have hx' : (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ) ≤
      (((Ideal.absNorm v.asIdeal : NNReal) ^ n : NNReal) : ℝ) := by
    rw [NumberField.FinitePlace.norm_def v x] at hx
    exact_mod_cast hx
  have hkey : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) ≤
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) := by
    rw [hexp]
    exact NNReal.coe_le_coe.mp hx'
  have hmono := WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (v := v))
  exact hmono.le_iff_le.mp hkey

private theorem norm_eq_one_of_valued_eq_one {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def v u, hu, map_one, NNReal.coe_one]

private theorem modulus_real_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem valued_eq_one_of_valued_sub_one_le {u : v.adicCompletion ℚ} {k : ℕ} (hk : 1 ≤ k)
    (hu : Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ))) : Valued.v u = 1 := by
  have hlt : Valued.v (u - 1) < Valued.v (1 : v.adicCompletion ℚ) := by
    rw [Valuation.map_one]
    refine lt_of_le_of_lt hu ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have h := Valued.v.map_add_eq_of_lt_right hlt
  rwa [sub_add_cancel, Valuation.map_one] at h

private theorem exists_forall_charExt_mul_eq (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    ∃ k : ℕ, ∀ u w : v.adicCompletion ℚ,
      Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ)) → charExt η (u * w) = charExt η w := by
  obtain ⟨c, hc⟩ := exists_hasConductorExponentAt_of_continuous ℚ v η hη.continuous
  refine ⟨max c 1, fun u w huk => ?_⟩
  have hu1 : Valued.v u = 1 := valued_eq_one_of_valued_sub_one_le v (le_max_right c 1) huk
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu1
  have hmem : Units.mk0 u hu0 ∈ higherUnitsAt ℚ v c := by
    rw [mem_higherUnitsAt_iff, Units.val_mk0]
    refine ⟨hu1, Or.inr (huk.trans ?_)⟩
    exact WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast le_max_left c 1))
  have hη1 : η (Units.mk0 u hu0) = 1 := hc.1 _ hmem
  by_cases hw : w = 0
  · rw [hw, mul_zero]
  have hcoe : u * w = ((Units.mk0 u hu0 * Units.mk0 w hw : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
  rw [hcoe, charExt_coe_units, map_mul, hη1, one_mul, ← charExt_coe_units, Units.val_mk0]

private theorem isClosed_valued_le (n : ℤ) : IsClosed {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x | Valued.v.restrict x ≤ Valued.v.restrict y₀} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_le_iff, hy₀]
  rw [hset]
  exact Valued.isClosed_closedBall _ _

private theorem measurableSet_unipotentBall3 (c : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (unipotentBall3 v c) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hset : unipotentBall3 v c =
      (Prod.fst ⁻¹' {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.1) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.2) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (2 * c)}) := by
    ext p
    simp only [unipotentBall3, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  rw [hset]
  exact (((isClosed_valued_le v c).measurableSet.preimage measurable_fst).inter
    ((isClosed_valued_le v c).measurableSet.preimage (measurable_fst.comp measurable_snd))).inter
    ((isClosed_valued_le v (2 * c)).measurableSet.preimage (measurable_snd.comp measurable_snd))

end TorusValues

end WeylTranslateZeta
end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal

open Polynomial in

private def IsLaurentInQPow (q : ℂ) (P : ℂ → ℂ) : Prop :=
  ∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ, P s = Q.eval (q ^ (-s)) * q ^ ((m : ℂ) * s)

namespace IsLaurentInQPow

variable {q : ℂ}

private theorem mul (hq : q ≠ 0) {P₁ P₂ : ℂ → ℂ} (h₁ : IsLaurentInQPow q P₁) (h₂ : IsLaurentInQPow q P₂) :
    IsLaurentInQPow q fun s => P₁ s * P₂ s := by
  obtain ⟨Q₁, m₁, e₁⟩ := h₁
  obtain ⟨Q₂, m₂, e₂⟩ := h₂
  refine ⟨Q₁ * Q₂, m₁ + m₂, fun s => ?_⟩
  show P₁ s * P₂ s = _
  rw [e₁ s, e₂ s, Polynomial.eval_mul, Nat.cast_add, add_mul, Complex.cpow_add _ _ hq]
  ring

private theorem qpow_add_nat_mul_mul_pow (hq : q ≠ 0) (m k : ℕ) (s : ℂ) :
    q ^ (((m + k : ℕ) : ℂ) * s) * (q ^ (-s)) ^ k = q ^ ((m : ℂ) * s) := by
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq]
  congr 1
  push_cast
  ring

private theorem add (hq : q ≠ 0) {P₁ P₂ : ℂ → ℂ} (h₁ : IsLaurentInQPow q P₁) (h₂ : IsLaurentInQPow q P₂) :
    IsLaurentInQPow q fun s => P₁ s + P₂ s := by
  obtain ⟨Q₁, m₁, e₁⟩ := h₁
  obtain ⟨Q₂, m₂, e₂⟩ := h₂
  refine ⟨Q₁ * Polynomial.X ^ m₂ + Q₂ * Polynomial.X ^ m₁, m₁ + m₂, fun s => ?_⟩
  show P₁ s + P₂ s = _
  rw [e₁ s, e₂ s, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_pow, Polynomial.eval_X, add_mul]
  have h₁' := qpow_add_nat_mul_mul_pow hq m₁ m₂ s
  have h₂' := qpow_add_nat_mul_mul_pow hq m₂ m₁ s
  rw [add_comm m₂ m₁] at h₂'
  rw [← h₁', ← h₂']
  ring

end IsLaurentInQPow

namespace LaurentZetaSlot

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem _root_.LaurentZetaSlot.absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by
  intro h0
  have h := one_lt_absNorm_real v
  rw [h0] at h
  norm_num at h

p2m_export "LaurentZetaSlot" "absNorm_ne_zero"

private def shell (j : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x = WithZero.exp (-j)}

private theorem modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    modulus x = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-j) := by
  have hnorm : ‖x‖ = ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ≥0) : ℝ) :=
    FinitePlace.norm_def v x
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x]
  apply NNReal.coe_injective
  rw [coe_nnnorm, hnorm, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have htoAdd : ∀ h : WithZero.exp (-j) ≠ (0 : WithZero (Multiplicative ℤ)),
      Multiplicative.toAdd (WithZero.unzero h) = -j := fun _ => rfl
  rw [htoAdd]

private def unitShell : Set (v.adicCompletion ℚ) := {x | Valued.v x = 1}

private theorem isAddHaarMeasure_selfDualHaarAt' : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  exact WeylTranslateZeta.isAddHaarMeasure_selfDualHaarAt ℚ v

private theorem sFinite_mulMeasure_selfDualHaarAt' : SFinite (mulMeasure (selfDualHaarAt ℚ v)) := by
  exact WeylTranslateZeta.sFinite_mulMeasure_selfDualHaarAt ℚ v

attribute [local instance] sFinite_mulMeasure_selfDualHaarAt'

private theorem isClopen_shell (j : ℤ) : IsClopen (shell v j) := by
  obtain ⟨x₀, hx₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp (-j))
  have hset : shell v j = {x | Valued.v.restrict x = Valued.v.restrict x₀} := by
    ext x
    simp only [shell, Set.mem_setOf_eq, Valuation.restrict_inj, hx₀]
  have hne : Valued.v.restrict x₀ ≠ 0 := by
    intro h0
    have h1 : Valued.v x₀ = Valued.v (0 : v.adicCompletion ℚ) :=
      (Valuation.restrict_inj Valued.v).mp (by rw [h0, map_zero])
    rw [map_zero, hx₀] at h1
    exact WithZero.exp_ne_zero h1
  rw [hset]
  exact Valued.isClopen_sphere _ hne

private theorem unitShell_eq_shell_zero : unitShell v = shell v 0 := by
  simp only [unitShell, shell, neg_zero, WithZero.exp_zero]

private theorem modulus_eq_one_of_mem_unitShell {x : v.adicCompletion ℚ} (hx : x ∈ unitShell v) : modulus x = 1 := by
  rw [unitShell_eq_shell_zero] at hx
  rw [modulus_eq_of_mem_shell v hx, neg_zero, zpow_zero]

private theorem isClopen_unitShell : IsClopen (unitShell v) := by
  rw [unitShell_eq_shell_zero]
  exact isClopen_shell v 0

private theorem measurableSet_unitShell : MeasurableSet (unitShell v) :=
  (isClopen_unitShell v).isOpen.measurableSet

private theorem unitShell_subset_integers : unitShell v ⊆ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  fun x hx => by
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact le_of_eq hx

private theorem isCompact_unitShell : IsCompact (unitShell v) := by
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  exact hO.of_isClosed_subset (isClopen_unitShell v).isClosed (unitShell_subset_integers v)

private theorem mulMeasure_unitShell
    : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) = selfDualHaarAt ℚ v (unitShell v) := by
  rw [mulMeasure, withDensity_apply _ (measurableSet_unitShell v),
    Measure.restrict_restrict (measurableSet_unitShell v)]
  have hsub : unitShell v ∩ {(0 : v.adicCompletion ℚ)}ᶜ = unitShell v := by
    refine Set.inter_eq_left.mpr fun x hx => ?_
    rintro rfl
    simp [unitShell] at hx
  rw [hsub]
  calc ∫⁻ x in unitShell v, ((modulus x : ℝ≥0∞))⁻¹ ∂(selfDualHaarAt ℚ v)
      = ∫⁻ _ in unitShell v, (1 : ℝ≥0∞) ∂(selfDualHaarAt ℚ v) := by
        refine setLIntegral_congr_fun (measurableSet_unitShell v) fun x hx => ?_
        rw [modulus_eq_one_of_mem_unitShell v hx]
        simp
    _ = selfDualHaarAt ℚ v (unitShell v) := by simp

private theorem mulMeasure_unitShell_lt_top : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) < ⊤ := by
  haveI := isAddHaarMeasure_selfDualHaarAt' v
  rw [mulMeasure_unitShell]
  exact (isCompact_unitShell v).measure_lt_top

private scoped instance isFiniteMeasure_restrict_unitShell :
    IsFiniteMeasure ((mulMeasure (selfDualHaarAt ℚ v)).restrict (unitShell v)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact mulMeasure_unitShell_lt_top v⟩

private noncomputable def twistedDiff (α : ℂ) (f : v.adicCompletion ℚ → ℂ) : v.adicCompletion ℚ → ℂ :=
  fun a => f a - α * f (a / (uniformizerUnit ℚ v : v.adicCompletion ℚ))

private noncomputable def slotScalar (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) : ℂ :=
  by classical exact if HasConductorExponentAt ℚ v η 0 then (η (uniformizerUnit ℚ v) : ℂ) else 0

private noncomputable def twistedDiff₃ (α : Fin 3 → ℂ) (f : v.adicCompletion ℚ → ℂ) : v.adicCompletion ℚ → ℂ :=
  twistedDiff v (α 0) (twistedDiff v (α 1) (twistedDiff v (α 2) f))

private noncomputable def unitProj (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f : v.adicCompletion ℚ → ℂ) :
    v.adicCompletion ℚ → ℂ :=
  fun a => (∫ w in unitShell v, f (a * w) * charExt χ w ∂(mulMeasure (selfDualHaarAt ℚ v))) /
    (((mulMeasure (selfDualHaarAt ℚ v)).real (unitShell v) : ℝ) : ℂ)

end LaurentZetaSlot
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal NumberField.StandardAddChar
open NumberField.AdelicLevel
open LaurentZetaSlot (twistedDiff twistedDiff₃ unitProj slotScalar unitShell)
open scoped Topology NNReal ENNReal

section TorusCollapse

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

section CellPoint

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

end CellPoint
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section Truncated

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

end Truncated
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section Projection

variable (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)

end Projection
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section Covariances

private def IsTestAdditive (T : ((Fin 3 → v.adicCompletion ℚ) → ℂ) → v.adicCompletion ℚ → ℂ) : Prop :=
  ∀ Φ Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → IsLocallyConstant Ψ →
    HasCompactSupport Ψ → ∀ t : v.adicCompletion ℚ, T (Φ + Ψ) t = T Φ t + T Ψ t

variable (φA φB : (Fin 3 → v.adicCompletion ℚ) → v.adicCompletion ℚ)

variable (T : ((Fin 3 → v.adicCompletion ℚ) → ℂ) → v.adicCompletion ℚ → ℂ)

variable {T}

variable {v} in

private theorem IsTestAdditive.sub (hadd : IsTestAdditive v T) {Φ Ψ : (Fin 3 → v.adicCompletion ℚ) → ℂ}
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (hΨl : IsLocallyConstant Ψ)
    (hΨc : HasCompactSupport Ψ) (t : v.adicCompletion ℚ) : T (Φ - Ψ) t = T Φ t - T Ψ t := by
  have h := hadd (Φ - Ψ) Ψ (hΦl.sub hΨl) (hΦc.sub hΨc) hΨl hΨc t
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

end Covariances
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section Strata

variable {φA φB : (Fin 3 → v.adicCompletion ℚ) → v.adicCompletion ℚ}
variable {T : ((Fin 3 → v.adicCompletion ℚ) → ℂ) → v.adicCompletion ℚ → ℂ}
variable {χA χB : (v.adicCompletion ℚ)ˣ →* ℂˣ}

end Strata
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section Covariant

variable {φA φB : (Fin 3 → v.adicCompletion ℚ) → v.adicCompletion ℚ}
variable {T : ((Fin 3 → v.adicCompletion ℚ) → ℂ) → v.adicCompletion ℚ → ℂ}
variable {σL : (v.adicCompletion ℚ)ˣ → (Fin 3 → v.adicCompletion ℚ) → (Fin 3 → v.adicCompletion ℚ)}
variable {χL χA χB : (v.adicCompletion ℚ)ˣ →* ℂˣ}

end Covariant
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section Torus

variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

variable (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

end Torus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

end TorusCollapse
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar
open scoped Topology

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section DualTorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def dualPoint (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : LocalGL3 v :=
  longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
    antidiagonal3 v

private noncomputable def dualTranslate (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : LocalGL3 v → ℂ :=
  gl3AmbientRightTranslate (R := ℂ) (dualPoint v a x) (cellSectionOf v ν Φ)

private theorem dualTranslate_apply (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) (h : LocalGL3 v) :
    dualTranslate v ν Φ a x h = cellSectionOf v ν Φ (h * dualPoint v a x) :=
  rfl

open Classical in

private noncomputable def dualFn : v.adicCompletion ℚ → ℂ := fun t =>
  letI := localBorel ℚ v
  if h : t = 0 then 0 else
    (∫ x : v.adicCompletion ℚ, jacquetValue v (dualTranslate v ν Φ (Units.mk0 t h) x) ∂(selfDualHaarAt ℚ v)) *
      ((modulus t : ℝ) : ℂ)⁻¹

private theorem dualFn_zero : dualFn v ν Φ 0 = 0 := by
  simp [dualFn]

private theorem dualFn_coe_units (a : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    dualFn v ν Φ a =
      (∫ x : v.adicCompletion ℚ, jacquetValue v (dualTranslate v ν Φ a x) ∂(selfDualHaarAt ℚ v)) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ := by
  simp [dualFn, a.ne_zero]

end DualTorusValues
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section RightUnipotent

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem gl3Entry_mul_upperUnipotent3_zero (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (h * upperUnipotent3 x y z) i 0 = gl3Entry v h i 0 := by
  simp [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_one (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (h * upperUnipotent3 x y z) i 1 = gl3Entry v h i 0 * x + gl3Entry v h i 1 := by
  simp [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_two (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (h * upperUnipotent3 x y z) i 2 = gl3Entry v h i 0 * z + gl3Entry v h i 1 * y + gl3Entry v h i 2 := by
  simp [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem cornerEntry_mul_upperUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    cornerEntry v (h * upperUnipotent3 x y z) = cornerEntry v h := by
  unfold cornerEntry
  exact gl3Entry_mul_upperUnipotent3_zero v h x y z 2

private theorem lowerMinor_mul_upperUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    lowerMinor v (h * upperUnipotent3 x y z) = lowerMinor v h := by
  simp only [lowerMinor, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_one]
  ring

private theorem outerMinor_mul_upperUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    outerMinor v (h * upperUnipotent3 x y z) = outerMinor v h + y * lowerMinor v h := by
  simp only [outerMinor, lowerMinor, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_two]
  ring

private theorem gl3Det_mul_upperUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    gl3Det v (h * upperUnipotent3 x y z) = gl3Det v h := by
  have hdet : (!![(1 : v.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1]).det = 1 := by
    simp [Matrix.det_fin_three]
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, upperUnipotent3_coe, hdet, mul_one]

private theorem mul_upperUnipotent3_mem_bigCell3_iff (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    h * upperUnipotent3 x y z ∈ bigCell3 v ↔ h ∈ bigCell3 v := by
  simp only [mem_bigCell3_iff, cornerEntry_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3]

private theorem cellValue_mul_upperUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    cellValue v ν (h * upperUnipotent3 x y z) = cellValue v ν h := by
  simp only [cellValue, gl3Det_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3, cornerEntry_mul_upperUnipotent3]

private theorem cellRatio_apply_zero (g : LocalGL3 v) : cellRatio v g 0 = gl3Entry v g 2 1 / cornerEntry v g := rfl

private theorem cellRatio_apply_one (g : LocalGL3 v) : cellRatio v g 1 = gl3Entry v g 2 2 / cornerEntry v g := rfl

private theorem cellRatio_apply_two (g : LocalGL3 v) : cellRatio v g 2 = outerMinor v g / lowerMinor v g := rfl

private theorem cellRatio_mul_upperUnipotent3 {h : LocalGL3 v} (hc : cornerEntry v h ≠ 0) (hl : lowerMinor v h ≠ 0)
    (x y z : v.adicCompletion ℚ) :
    cellRatio v (h * upperUnipotent3 x y z) =
      ![cellRatio v h 0 + x, cellRatio v h 1 + (z + y * cellRatio v h 0), cellRatio v h 2 + y] := by
  have hc' : gl3Entry v h 2 0 ≠ 0 := hc
  ext i
  match i with
  | 0 =>
      change cellRatio v (h * upperUnipotent3 x y z) 0 = cellRatio v h 0 + x
      rw [cellRatio_apply_zero, cellRatio_apply_zero, cornerEntry_mul_upperUnipotent3,
        gl3Entry_mul_upperUnipotent3_one]
      unfold cornerEntry
      field_simp
      ring1
  | 1 =>
      change cellRatio v (h * upperUnipotent3 x y z) 1 = cellRatio v h 1 + (z + y * cellRatio v h 0)
      rw [cellRatio_apply_one, cellRatio_apply_one, cellRatio_apply_zero, cornerEntry_mul_upperUnipotent3,
        gl3Entry_mul_upperUnipotent3_two]
      unfold cornerEntry
      field_simp
      ring1
  | 2 =>
      change cellRatio v (h * upperUnipotent3 x y z) 2 = cellRatio v h 2 + y
      rw [cellRatio_apply_two, cellRatio_apply_two, outerMinor_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3]
      field_simp

private theorem exists_forall_cellSectionOf_mul_upperUnipotent3
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (h : LocalGL3 v) (x y z : v.adicCompletion ℚ), ‖x‖ ≤ ε → ‖y‖ ≤ ε → ‖z‖ ≤ ε →
      cellSectionOf v ν Φ (h * upperUnipotent3 x y z) = cellSectionOf v ν Φ h := by
  obtain ⟨r, hr, hrΦ⟩ := exists_invariance_radius v Φ hΦl hΦc
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  set R' : ℝ := max R 1 with hR'_def
  have hR'1 : (1 : ℝ) ≤ R' := le_max_right _ _
  have hR'0 : (0 : ℝ) < R' := zero_lt_one.trans_le hR'1
  set ε : ℝ := min 1 (r / R') with hε_def
  have hε0 : 0 < ε := lt_min zero_lt_one (div_pos hr hR'0)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεr : ε * R' ≤ r := by
    calc ε * R' ≤ r / R' * R' := by gcongr; exact min_le_right _ _
      _ = r := div_mul_cancel₀ r hR'0.ne'
  have hεr' : ε ≤ r := by
    calc ε = ε * 1 := (mul_one ε).symm
      _ ≤ ε * R' := by gcongr
      _ ≤ r := hεr
  refine ⟨ε, hε0, fun h x y z hx hy hz => ?_⟩
  by_cases hg : h ∈ bigCell3 v
  · have hg' : h * upperUnipotent3 x y z ∈ bigCell3 v := (mul_upperUnipotent3_mem_bigCell3_iff v h x y z).mpr hg
    obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v h).mp hg
    rw [cellSectionOf_apply_of_mem v ν Φ hg', cellSectionOf_apply_of_mem v ν Φ hg, cellValue_mul_upperUnipotent3]
    have hq := cellRatio_mul_upperUnipotent3 v hc hl x y z
    by_cases hzero : Φ (cellRatio v h) = 0 ∧ Φ (cellRatio v (h * upperUnipotent3 x y z)) = 0
    · rw [hzero.1, hzero.2]
    ·
      have h0 : ‖cellRatio v h 0‖ ≤ R' := by
        rcases not_and_or.mp hzero with h1 | h2
        · exact (hR _ h1 0).trans (le_max_left _ _)
        · have hb : ‖cellRatio v (h * upperUnipotent3 x y z) 0‖ ≤ R := hR _ h2 0
          have he : cellRatio v h 0 = cellRatio v (h * upperUnipotent3 x y z) 0 + -x := by
            rw [hq]
            simp
          rw [he]
          calc ‖cellRatio v (h * upperUnipotent3 x y z) 0 + -x‖
                ≤ max ‖cellRatio v (h * upperUnipotent3 x y z) 0‖ ‖-x‖ := IsUltrametricDist.norm_add_le_max _ _
            _ ≤ max R 1 := by
                rw [norm_neg]
                exact max_le_max hb (hx.trans hε1)
      congr 1
      apply hrΦ
      intro i
      rw [hq]
      fin_cases i
      · simpa using hx.trans hεr'
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, add_sub_cancel_left]
        calc ‖z + y * cellRatio v h 0‖ ≤ max ‖z‖ ‖y * cellRatio v h 0‖ := IsUltrametricDist.norm_add_le_max _ _
          _ ≤ max ε (ε * R') := by
              apply max_le_max hz
              rw [norm_mul]
              exact mul_le_mul hy h0 (norm_nonneg _) hε0.le
          _ ≤ ε * R' := max_le (le_mul_of_one_le_right hε0.le hR'1) le_rfl
          _ ≤ r := hεr
      · simpa using hy.trans hεr'
  · rw [cellSectionOf_apply_of_notMem v ν Φ
        (fun h' => hg ((mul_upperUnipotent3_mem_bigCell3_iff v h x y z).mp h')),
      cellSectionOf_apply_of_notMem v ν Φ hg]

private theorem preimage_add_unipotentBall3_of_mem {c : ℤ}
    {e : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ} (he : e ∈ unipotentBall3 v c) :
    (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p + e) ⁻¹' unipotentBall3 v c =
      unipotentBall3 v c := by
  simp only [mem_unipotentBall3_iff] at he
  obtain ⟨he1, he2, he3⟩ := he
  ext p
  simp only [Set.mem_preimage, mem_unipotentBall3_iff, Prod.fst_add, Prod.snd_add]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [show p.1 = (p.1 + e.1) + -e.1 by ring]
      exact (Valuation.map_add _ _ _).trans (max_le h1 (by rwa [Valuation.map_neg]))
    · rw [show p.2.1 = (p.2.1 + e.2.1) + -e.2.1 by ring]
      exact (Valuation.map_add _ _ _).trans (max_le h2 (by rwa [Valuation.map_neg]))
    · rw [show p.2.2 = (p.2.2 + e.2.2) + -e.2.2 by ring]
      exact (Valuation.map_add _ _ _).trans (max_le h3 (by rwa [Valuation.map_neg]))
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(Valuation.map_add _ _ _).trans (max_le h1 he1), (Valuation.map_add _ _ _).trans (max_le h2 he2),
      (Valuation.map_add _ _ _).trans (max_le h3 he3)⟩

private theorem setIntegral_unipotentBall3_add_of_mem {c : ℤ}
    {e : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ} (he : e ∈ unipotentBall3 v c)
    (F : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ p in unipotentBall3 v c, F (p + e) ∂(jacquetHaar3 v) = ∫ p in unipotentBall3 v c, F p ∂(jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI := sFinite_selfDualHaarAt ℚ v
  have hmeas := measurableSet_unipotentBall3 v c
  have hpre := preimage_add_unipotentBall3_of_mem v he
  have key : (unipotentBall3 v c).indicator (fun p => F (p + e)) =
      fun p => (unipotentBall3 v c).indicator F (p + e) := by
    funext p
    by_cases hp : p ∈ unipotentBall3 v c
    · have hp' : p + e ∈ unipotentBall3 v c := by
        rw [← hpre] at hp
        exact hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp']
    · have hp' : p + e ∉ unipotentBall3 v c := by
        rw [← hpre] at hp
        exact hp
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
  unfold jacquetHaar3
  rw [← integral_indicator hmeas, ← integral_indicator hmeas, key, integral_add_right_eq_self]

private theorem exists_nat_valued_le_exp (x : v.adicCompletion ℚ) : ∃ N : ℕ, Valued.v x ≤ WithZero.exp (N : ℤ) := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖x‖ (one_lt_absNorm_real v)
  refine ⟨N, valued_le_of_norm_le_zpow v ?_⟩
  rw [zpow_natCast]
  exact hN.le

private theorem jacquetValue_rightTranslate_upperUnipotent3_mul (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (g : LocalGL3 v) (e₁ e₃ : v.adicCompletion ℚ) :
    jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 e₁ 0 e₃ * g) (cellSectionOf v ν Φ)) =
      psiLocal ℚ v e₁ * jacquetValue v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ)) := by
  letI := localBorel ℚ v
  set f₁ := gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 e₁ 0 e₃ * g) (cellSectionOf v ν Φ) with hf₁
  set f₀ := gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ) with hf₀
  obtain ⟨c₁, h₁⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩
    (upperUnipotent3 e₁ 0 e₃ * g)
  obtain ⟨c₀, h₀⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩ g
  obtain ⟨N₁, hN₁⟩ := exists_nat_valued_le_exp v e₁
  obtain ⟨N₃, hN₃⟩ := exists_nat_valued_le_exp v e₃

  set c : ℤ := max (max (c₁ : ℤ) (c₀ : ℤ)) (max (N₁ : ℤ) (N₃ : ℤ)) with hc_def
  have hc₁ : (c₁ : ℤ) ≤ c := (le_max_left _ _).trans (le_max_left _ _)
  have hc₀ : (c₀ : ℤ) ≤ c := (le_max_right _ _).trans (le_max_left _ _)
  have hcN₁ : (N₁ : ℤ) ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcN₃ : (N₃ : ℤ) ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hc0 : (0 : ℤ) ≤ c := (Int.natCast_nonneg N₁).trans hcN₁
  have hst₁ : ∃ c' : ℕ, ∀ c : ℤ, (c' : ℤ) ≤ c → jacquetTruncated3 v c f₁ = jacquetTruncated3 v c' f₁ :=
    ⟨c₁, fun c hc => (h₁ c hc).2⟩
  have hst₀ : ∃ c' : ℕ, ∀ c : ℤ, (c' : ℤ) ≤ c → jacquetTruncated3 v c f₀ = jacquetTruncated3 v c' f₀ :=
    ⟨c₀, fun c hc => (h₀ c hc).2⟩
  have hlev₁ : (jacquetLevel v f₁ : ℤ) ≤ c :=
    (Int.ofNat_le.mpr (jacquetLevel_le v f₁ fun c hc => (h₁ c hc).2)).trans hc₁
  have hlev₀ : (jacquetLevel v f₀ : ℤ) ≤ c :=
    (Int.ofNat_le.mpr (jacquetLevel_le v f₀ fun c hc => (h₀ c hc).2)).trans hc₀
  rw [← jacquetTruncated3_eq_jacquetValue v f₁ hst₁ hlev₁, ← jacquetTruncated3_eq_jacquetValue v f₀ hst₀ hlev₀]

  have he : ((e₁, (0 : v.adicCompletion ℚ), e₃) : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) ∈
      unipotentBall3 v c := by
    simp only [mem_unipotentBall3_iff, Valuation.map_zero]
    refine ⟨hN₁.trans (WithZero.exp_le_exp.mpr hcN₁), zero_le', hN₃.trans (WithZero.exp_le_exp.mpr ?_)⟩
    omega

  set G : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ :=
    fun p => psiLocal ℚ v (-(p.1 + p.2.1)) * f₀ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) with hG
  have hint : ∀ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
      psiLocal ℚ v (-(p.1 + p.2.1)) * f₁ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) =
        psiLocal ℚ v e₁ * G (p + (e₁, (0 : v.adicCompletion ℚ), e₃)) := by
    intro p
    simp only [hG, hf₁, hf₀, gl3AmbientRightTranslate_apply, Prod.fst_add, Prod.snd_add, add_zero]
    rw [show antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * (upperUnipotent3 e₁ 0 e₃ * g) =
        antidiagonal3 v * upperUnipotent3 (p.1 + e₁) p.2.1 (p.2.2 + e₃) * g by
      rw [← mul_assoc, mul_assoc (antidiagonal3 v), upperUnipotent3_mul_upperUnipotent3, add_zero, mul_zero,
        add_zero]]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  unfold jacquetTruncated3
  simp_rw [hint]
  rw [integral_const_mul, setIntegral_unipotentBall3_add_of_mem v he]

end RightUnipotent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section DualValueSupport

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem dualPoint_mul_upperUnipotent3 (a : (v.adicCompletion ℚ)ˣ) (x t : v.adicCompletion ℚ) :
    dualPoint v a x * upperUnipotent3 0 t 0 = upperUnipotent3 (t * x) 0 (t * a) * dualPoint v a x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, upperUnipotent3_coe, upperUnipotent3_coe,
    show ((dualPoint v a x : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x), 0,
        ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] from coe_dualPoint_mul_antidiagonal3 v a x]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  field_simp
  ring1

private theorem exists_forall_lt_norm_jacquetValue_dualTranslate_eq_zero (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ X₀ : ℝ, ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), X₀ < ‖x‖ →
      jacquetValue v (dualTranslate v ν Φ a x) = 0 := by
  obtain ⟨ε, hε, hU⟩ := exists_forall_cellSectionOf_mul_upperUnipotent3 v ν Φ hΦl hΦc
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : v.adicCompletion ℚ, psiLocal ℚ v w₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact psiLocal_ne_one ℚ v (AddChar.ext _ _ h)
  refine ⟨‖w₀‖ / ε, fun a x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := (div_nonneg (norm_nonneg _) hε.le).trans_lt hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
  set t : v.adicCompletion ℚ := w₀ / x with ht_def
  have ht : ‖t‖ ≤ ε := by
    rw [ht_def, norm_div, div_le_iff₀ hxpos]
    have := (div_lt_iff₀ hε).mp hx
    linarith [mul_comm ε ‖x‖]
  have htx : t * x = w₀ := div_mul_cancel₀ w₀ hx0

  have h1 : gl3AmbientRightTranslate (R := ℂ) (dualPoint v a x * upperUnipotent3 0 t 0) (cellSectionOf v ν Φ) =
      dualTranslate v ν Φ a x := by
    funext h
    rw [dualTranslate_apply, gl3AmbientRightTranslate_apply, ← mul_assoc]
    exact hU _ 0 t 0 (by simpa using hε.le) ht (by simpa using hε.le)
  have h2 := jacquetValue_rightTranslate_upperUnipotent3_mul v ν Φ hν hΦl hΦc (dualPoint v a x) (t * x) (t * a)
  rw [← dualPoint_mul_upperUnipotent3, h1, htx] at h2
  have h3 : jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (dualPoint v a x) (cellSectionOf v ν Φ)) =
      jacquetValue v (dualTranslate v ν Φ a x) := rfl
  rw [h3] at h2

  have h4 : (1 - psiLocal ℚ v w₀) * jacquetValue v (dualTranslate v ν Φ a x) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd (sub_eq_zero.mp h5).symm hw₀
  · exact h5

end DualValueSupport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

private def lowerUnipotent3 {A : Type*} [CommRing A] (x y z : A) : GL (Fin 3) A where
  val := !![1, 0, 0; x, 1, 0; z, y, 1]
  inv := !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    ring

@[scoped simp] private theorem lowerUnipotent3_coe {A : Type*} [CommRing A] (x y z : A) :
    ((lowerUnipotent3 x y z : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![1, 0, 0; x, 1, 0; z, y, 1] :=
  rfl

private theorem lowerUnipotent3_mul_lowerUnipotent3 {A : Type*} [CommRing A] (x y z x' y' z' : A) :
    lowerUnipotent3 x y z * lowerUnipotent3 x' y' z' = lowerUnipotent3 (x + x') (y + y') (z + z' + y * x') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem mul_lowerUnipotent3_mul_lowerUnipotent3_neg {A : Type*} [CommRing A] (h : GL (Fin 3) A) (x y z : A) :
    h * lowerUnipotent3 x y z * lowerUnipotent3 (-x) (-y) (x * y - z) = h := by
  rw [mul_assoc, lowerUnipotent3_mul_lowerUnipotent3, show x + -x = 0 by ring, show y + -y = 0 by ring,
    show z + (x * y - z) + y * -x = 0 by ring]
  have h1 : (lowerUnipotent3 0 0 0 : GL (Fin 3) A) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotent3]
  rw [h1, mul_one]

section RightLower

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def innerMinor (g : LocalGL3 v) : v.adicCompletion ℚ :=
  gl3Entry v g 1 1 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 1

private theorem cornerEntry_mul_innerMinor (g : LocalGL3 v) :
    cornerEntry v g * innerMinor v g = outerMinor v g * gl3Entry v g 2 1 - lowerMinor v g * gl3Entry v g 2 2 := by
  simp only [cornerEntry, innerMinor, outerMinor, lowerMinor]
  ring

private theorem gl3Entry_mul_lowerUnipotent3_zero (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (h * lowerUnipotent3 x y z) i 0 = gl3Entry v h i 0 + gl3Entry v h i 1 * x + gl3Entry v h i 2 * z := by
  simp [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_lowerUnipotent3_one (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (h * lowerUnipotent3 x y z) i 1 = gl3Entry v h i 1 + gl3Entry v h i 2 * y := by
  simp [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_lowerUnipotent3_two (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (h * lowerUnipotent3 x y z) i 2 = gl3Entry v h i 2 := by
  simp [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem cornerEntry_mul_lowerUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    cornerEntry v (h * lowerUnipotent3 x y z) = cornerEntry v h + gl3Entry v h 2 1 * x + gl3Entry v h 2 2 * z := by
  unfold cornerEntry
  exact gl3Entry_mul_lowerUnipotent3_zero v h x y z 2

private theorem lowerMinor_mul_lowerUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    lowerMinor v (h * lowerUnipotent3 x y z) =
      lowerMinor v h + y * outerMinor v h + (x * y - z) * innerMinor v h := by
  simp only [lowerMinor, outerMinor, innerMinor, gl3Entry_mul_lowerUnipotent3_zero, gl3Entry_mul_lowerUnipotent3_one]
  ring

private theorem outerMinor_mul_lowerUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    outerMinor v (h * lowerUnipotent3 x y z) = outerMinor v h + x * innerMinor v h := by
  simp only [outerMinor, innerMinor, gl3Entry_mul_lowerUnipotent3_zero, gl3Entry_mul_lowerUnipotent3_two]
  ring

private theorem gl3Det_mul_lowerUnipotent3 (h : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    gl3Det v (h * lowerUnipotent3 x y z) = gl3Det v h := by
  have hdet : (!![(1 : v.adicCompletion ℚ), 0, 0; x, 1, 0; z, y, 1]).det = 1 := by
    simp [Matrix.det_fin_three]
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, lowerUnipotent3_coe, hdet, mul_one]

private theorem norm_sub_le_max_adic (a b : v.adicCompletion ℚ) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg, ← norm_neg b]
  exact IsUltrametricDist.norm_add_le_max a (-b)

private theorem exists_forall_cellSectionOf_mul_lowerUnipotent3_of_ne (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (h : LocalGL3 v) (x y z : v.adicCompletion ℚ), ‖x‖ ≤ ε → ‖y‖ ≤ ε → ‖z‖ ≤ ε →
      h ∈ bigCell3 v → Φ (cellRatio v h) ≠ 0 →
        cellSectionOf v ν Φ (h * lowerUnipotent3 x y z) = cellSectionOf v ν Φ h := by
  obtain ⟨r, hr, hrΦ⟩ := exists_invariance_radius v Φ hΦl hΦc
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  obtain ⟨k₀, hk₀⟩ := exists_forall_charExt_mul_eq v (ν 0) (hν 0)
  obtain ⟨k₁, hk₁⟩ := exists_forall_charExt_mul_eq v (ν 1) (hν 1)
  obtain ⟨k₂, hk₂⟩ := exists_forall_charExt_mul_eq v (ν 2) (hν 2)
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq_def
  have hq1 : (1 : ℝ) < q := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  set R' : ℝ := max R 1 with hR'_def
  have hR'1 : (1 : ℝ) ≤ R' := le_max_right _ _
  have hR'0 : (0 : ℝ) < R' := zero_lt_one.trans_le hR'1
  have hRR' : R ≤ R' := le_max_left _ _
  set k : ℕ := max (max k₀ k₁) (max k₂ 1) with hk_def
  have hk1 : 1 ≤ k := (le_max_right _ _).trans (le_max_right _ _)
  have hkk₀ : k₀ ≤ k := (le_max_left _ _).trans (le_max_left _ _)
  have hkk₁ : k₁ ≤ k := (le_max_right _ _).trans (le_max_left _ _)
  have hkk₂ : k₂ ≤ k := (le_max_left _ _).trans (le_max_right _ _)
  set ε : ℝ := min (min 1 (r / R' ^ 3)) (q ^ (-(k : ℤ)) / R' ^ 2) with hε_def
  have hε0 : 0 < ε :=
    lt_min (lt_min zero_lt_one (div_pos hr (by positivity))) (div_pos (zpow_pos hq0 _) (by positivity))
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hεr : ε * R' ^ 3 ≤ r := by
    calc ε * R' ^ 3 ≤ r / R' ^ 3 * R' ^ 3 := by gcongr; exact (min_le_left _ _).trans (min_le_right _ _)
      _ = r := div_mul_cancel₀ r (by positivity)
  have hεk : ε * R' ^ 2 ≤ q ^ (-(k : ℤ)) := by
    calc ε * R' ^ 2 ≤ q ^ (-(k : ℤ)) / R' ^ 2 * R' ^ 2 := by gcongr; exact min_le_right _ _
      _ = q ^ (-(k : ℤ)) := div_mul_cancel₀ _ (by positivity)
  refine ⟨ε, hε0, fun h x y z hx hy hz hg hΦ => ?_⟩
  obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v h).mp hg

  set c := cornerEntry v h with hc_def
  set ℓ := lowerMinor v h with hℓ_def
  set o := outerMinor v h with ho_def
  set D := gl3Det v h with hD_def
  set r₀ := cellRatio v h 0 with hr₀_def
  set r₁ := cellRatio v h 1 with hr₁_def
  set r₂ := cellRatio v h 2 with hr₂_def
  have hr₀e : r₀ = gl3Entry v h 2 1 / c := cellRatio_apply_zero v h
  have hr₁e : r₁ = gl3Entry v h 2 2 / c := cellRatio_apply_one v h
  have hr₂e : r₂ = o / ℓ := cellRatio_apply_two v h
  have hQ₂₁ : gl3Entry v h 2 1 = r₀ * c := by rw [hr₀e, div_mul_cancel₀ _ hc]
  have hQ₂₂ : gl3Entry v h 2 2 = r₁ * c := by rw [hr₁e, div_mul_cancel₀ _ hc]
  have hoe : o = r₂ * ℓ := by rw [hr₂e, div_mul_cancel₀ _ hl]
  have hpe : innerMinor v h = (r₂ * r₀ - r₁) * ℓ := by
    have key := cornerEntry_mul_innerMinor v h
    rw [← hc_def, ← ho_def, ← hℓ_def, hQ₂₁, hQ₂₂, hoe] at key
    have : c * innerMinor v h = c * ((r₂ * r₀ - r₁) * ℓ) := by rw [key]; ring
    exact mul_left_cancel₀ hc this

  have hb : ∀ i, ‖cellRatio v h i‖ ≤ R' := fun i => (hR _ hΦ i).trans hRR'
  have hb₀ : ‖r₀‖ ≤ R' := hb 0
  have hb₁ : ‖r₁‖ ≤ R' := hb 1
  have hb₂ : ‖r₂‖ ≤ R' := hb 2
  have hbp : ‖r₂ * r₀ - r₁‖ ≤ R' ^ 2 := by
    calc ‖r₂ * r₀ - r₁‖ ≤ max ‖r₂ * r₀‖ ‖r₁‖ := norm_sub_le_max_adic v _ _
      _ ≤ max (R' * R') R' := by
          apply max_le_max _ hb₁
          rw [norm_mul]
          exact mul_le_mul hb₂ hb₀ (norm_nonneg _) hR'0.le
      _ = R' ^ 2 := by
          rw [max_eq_left (le_mul_of_one_le_right hR'0.le hR'1)]
          ring

  set uc : v.adicCompletion ℚ := 1 + r₀ * x + r₁ * z with huc_def
  set ul : v.adicCompletion ℚ := 1 + y * r₂ + (x * y - z) * (r₂ * r₀ - r₁) with hul_def
  have hxyz : ‖x * y - z‖ ≤ ε := by
    calc ‖x * y - z‖ ≤ max ‖x * y‖ ‖z‖ := norm_sub_le_max_adic v _ _
      _ ≤ max (ε * 1) ε := by
          apply max_le_max _ hz
          rw [norm_mul]
          exact mul_le_mul hx (hy.trans hε1) (norm_nonneg _) hε0.le
      _ = ε := by rw [mul_one, max_self]
  have huc1 : ‖uc - 1‖ ≤ q ^ (-(k : ℤ)) := by
    have : uc - 1 = r₀ * x + r₁ * z := by rw [huc_def]; ring
    rw [this]
    calc ‖r₀ * x + r₁ * z‖ ≤ max ‖r₀ * x‖ ‖r₁ * z‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (R' * ε) (R' * ε) := by
          apply max_le_max
          · rw [norm_mul]; exact mul_le_mul hb₀ hx (norm_nonneg _) hR'0.le
          · rw [norm_mul]; exact mul_le_mul hb₁ hz (norm_nonneg _) hR'0.le
      _ = ε * R' ^ 1 := by rw [max_self, pow_one, mul_comm]
      _ ≤ ε * R' ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR'1 (by norm_num)) hε0.le
      _ ≤ q ^ (-(k : ℤ)) := hεk
  have hul1 : ‖ul - 1‖ ≤ q ^ (-(k : ℤ)) := by
    have : ul - 1 = y * r₂ + (x * y - z) * (r₂ * r₀ - r₁) := by rw [hul_def]; ring
    rw [this]
    calc ‖y * r₂ + (x * y - z) * (r₂ * r₀ - r₁)‖
          ≤ max ‖y * r₂‖ ‖(x * y - z) * (r₂ * r₀ - r₁)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (ε * R') (ε * R' ^ 2) := by
          apply max_le_max
          · rw [norm_mul]; exact mul_le_mul hy hb₂ (norm_nonneg _) hε0.le
          · rw [norm_mul]; exact mul_le_mul hxyz hbp (norm_nonneg _) hε0.le
      _ ≤ ε * R' ^ 2 := by
          apply max_le _ le_rfl
          calc ε * R' = ε * R' ^ 1 := by rw [pow_one]
            _ ≤ ε * R' ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR'1 (by norm_num)) hε0.le
      _ ≤ q ^ (-(k : ℤ)) := hεk
  have hvuc : Valued.v (uc - 1) ≤ WithZero.exp (-(k : ℤ)) := valued_le_of_norm_le_zpow v huc1
  have hvul : Valued.v (ul - 1) ≤ WithZero.exp (-(k : ℤ)) := valued_le_of_norm_le_zpow v hul1
  have hvuc1 : Valued.v uc = 1 := valued_eq_one_of_valued_sub_one_le v hk1 hvuc
  have hvul1 : Valued.v ul = 1 := valued_eq_one_of_valued_sub_one_le v hk1 hvul
  have hnuc : ‖uc‖ = 1 := norm_eq_one_of_valued_eq_one v hvuc1
  have hnul : ‖ul‖ = 1 := norm_eq_one_of_valued_eq_one v hvul1
  have huc0 : uc ≠ 0 := fun h0 => by simp [h0] at hnuc
  have hul0 : ul ≠ 0 := fun h0 => by simp [h0] at hnul

  have hc' : cornerEntry v (h * lowerUnipotent3 x y z) = uc * c := by
    rw [cornerEntry_mul_lowerUnipotent3, ← hc_def, hQ₂₁, hQ₂₂, huc_def]
    ring
  have hℓ' : lowerMinor v (h * lowerUnipotent3 x y z) = ul * ℓ := by
    rw [lowerMinor_mul_lowerUnipotent3, ← hℓ_def, ← ho_def, hpe, hoe, hul_def]
    ring
  have ho' : outerMinor v (h * lowerUnipotent3 x y z) = (r₂ + x * (r₂ * r₀ - r₁)) * ℓ := by
    rw [outerMinor_mul_lowerUnipotent3, ← ho_def, hpe, hoe]
    ring
  have hD' : gl3Det v (h * lowerUnipotent3 x y z) = D := gl3Det_mul_lowerUnipotent3 v h x y z
  have hg' : h * lowerUnipotent3 x y z ∈ bigCell3 v := by
    rw [mem_bigCell3_iff, hc', hℓ']
    exact ⟨mul_ne_zero huc0 hc, mul_ne_zero hul0 hl⟩
  rw [cellSectionOf_apply_of_mem v ν Φ hg', cellSectionOf_apply_of_mem v ν Φ hg]

  have hmono : ∀ {k' : ℕ}, k' ≤ k → WithZero.exp (-(k : ℤ)) ≤ WithZero.exp (-(k' : ℤ)) := fun hk' =>
    WithZero.exp_le_exp.mpr (neg_le_neg (Int.ofNat_le.mpr hk'))
  congr 1
  ·
    rw [cellValue, cellValue, hc', hℓ', hD', ← hc_def, ← hℓ_def, ← hD_def]
    have e2 : charExt (ν 2) (uc * c) = charExt (ν 2) c := hk₂ uc c (hvuc.trans (hmono hkk₂))
    have e0 : charExt (ν 0) (D / (ul * ℓ)) = charExt (ν 0) (D / ℓ) := by
      rw [show D / (ul * ℓ) = ul⁻¹ * (D / ℓ) by field_simp]
      refine hk₀ ul⁻¹ (D / ℓ) ((le_of_eq ?_).trans (hvul.trans (hmono hkk₀)))
      rw [show ul⁻¹ - 1 = (1 - ul) / ul by field_simp, Valuation.map_div, hvul1, div_one, Valuation.map_sub_swap]
    have e1 : charExt (ν 1) (ul * ℓ / (uc * c)) = charExt (ν 1) (ℓ / c) := by
      rw [show ul * ℓ / (uc * c) = (ul / uc) * (ℓ / c) by field_simp]
      refine hk₁ (ul / uc) (ℓ / c) ((le_of_eq ?_).trans ((Valued.v.map_sub_le hvul hvuc).trans (hmono hkk₁)))
      rw [show ul / uc - 1 = ((ul - 1) - (uc - 1)) / uc by field_simp; ring1, Valuation.map_div, hvuc1, div_one]
    have en : (‖D / (ul * ℓ)‖ / ‖uc * c‖ : ℝ) = ‖D / ℓ‖ / ‖c‖ := by
      rw [norm_div, norm_mul, hnul, one_mul, norm_mul, hnuc, one_mul, norm_div]
    rw [e2, e0, e1, en]
  ·
    apply hrΦ
    have hR'2 : R' ≤ R' ^ 2 := by
      calc R' = R' ^ 1 := (pow_one _).symm
        _ ≤ R' ^ 2 := pow_le_pow_right₀ hR'1 (by norm_num)
    have hR'3 : R' ^ 2 ≤ R' ^ 3 := pow_le_pow_right₀ hR'1 (by norm_num)
    have hin : ‖r₀ * x + r₁ * z‖ ≤ ε * R' := by
      calc ‖r₀ * x + r₁ * z‖ ≤ max ‖r₀ * x‖ ‖r₁ * z‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max (R' * ε) (R' * ε) := by
            apply max_le_max
            · rw [norm_mul]; exact mul_le_mul hb₀ hx (norm_nonneg _) hR'0.le
            · rw [norm_mul]; exact mul_le_mul hb₁ hz (norm_nonneg _) hR'0.le
        _ = ε * R' := by rw [max_self, mul_comm]
    have hin' : ‖y * r₂ + (x * y - z) * (r₂ * r₀ - r₁)‖ ≤ ε * R' ^ 2 := by
      calc ‖y * r₂ + (x * y - z) * (r₂ * r₀ - r₁)‖
            ≤ max ‖y * r₂‖ ‖(x * y - z) * (r₂ * r₀ - r₁)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max (ε * R') (ε * R' ^ 2) := by
            apply max_le_max
            · rw [norm_mul]; exact mul_le_mul hy hb₂ (norm_nonneg _) hε0.le
            · rw [norm_mul]; exact mul_le_mul hxyz hbp (norm_nonneg _) hε0.le
        _ ≤ ε * R' ^ 2 := max_le (mul_le_mul_of_nonneg_left hR'2 hε0.le) le_rfl
    intro i
    match i with
    | 0 =>
        have e : cellRatio v (h * lowerUnipotent3 x y z) 0 - cellRatio v h 0 =
            (r₁ * y - r₀ * (r₀ * x + r₁ * z)) / uc := by
          rw [cellRatio_apply_zero, gl3Entry_mul_lowerUnipotent3_one, hc', ← hr₀_def, hQ₂₁, hQ₂₂, huc_def]
          rw [huc_def] at huc0
          field_simp
          ring1
        rw [e, norm_div, hnuc, div_one]
        calc ‖r₁ * y - r₀ * (r₀ * x + r₁ * z)‖ ≤ max ‖r₁ * y‖ ‖r₀ * (r₀ * x + r₁ * z)‖ := norm_sub_le_max_adic v _ _
          _ ≤ max (R' * ε) (R' * (ε * R')) := by
              apply max_le_max
              · rw [norm_mul]; exact mul_le_mul hb₁ hy (norm_nonneg _) hR'0.le
              · rw [norm_mul]; exact mul_le_mul hb₀ hin (norm_nonneg _) hR'0.le
          _ ≤ ε * R' ^ 3 := by
              apply max_le
              · calc R' * ε = ε * R' := mul_comm _ _
                  _ ≤ ε * R' ^ 3 := mul_le_mul_of_nonneg_left (hR'2.trans hR'3) hε0.le
              · calc R' * (ε * R') = ε * R' ^ 2 := by ring
                  _ ≤ ε * R' ^ 3 := mul_le_mul_of_nonneg_left hR'3 hε0.le
          _ ≤ r := hεr
    | 1 =>
        have e : cellRatio v (h * lowerUnipotent3 x y z) 1 - cellRatio v h 1 = -(r₁ * (r₀ * x + r₁ * z)) / uc := by
          rw [cellRatio_apply_one, gl3Entry_mul_lowerUnipotent3_two, hc', ← hr₁_def, hQ₂₂, huc_def]
          rw [huc_def] at huc0
          field_simp
          ring1
        rw [e, norm_div, norm_neg, hnuc, div_one]
        calc ‖r₁ * (r₀ * x + r₁ * z)‖ ≤ R' * (ε * R') := by
              rw [norm_mul]; exact mul_le_mul hb₁ hin (norm_nonneg _) hR'0.le
          _ = ε * R' ^ 2 := by ring
          _ ≤ ε * R' ^ 3 := mul_le_mul_of_nonneg_left hR'3 hε0.le
          _ ≤ r := hεr
    | 2 =>
        have e : cellRatio v (h * lowerUnipotent3 x y z) 2 - cellRatio v h 2 =
            (x * (r₂ * r₀ - r₁) - r₂ * (y * r₂ + (x * y - z) * (r₂ * r₀ - r₁))) / ul := by
          rw [cellRatio_apply_two, ho', hℓ', ← hr₂_def, mul_div_mul_right _ _ hl, div_sub' hul0, div_left_inj' hul0,
            hul_def]
          ring1
        rw [e, norm_div, hnul, div_one]
        calc ‖x * (r₂ * r₀ - r₁) - r₂ * (y * r₂ + (x * y - z) * (r₂ * r₀ - r₁))‖
              ≤ max ‖x * (r₂ * r₀ - r₁)‖ ‖r₂ * (y * r₂ + (x * y - z) * (r₂ * r₀ - r₁))‖ := norm_sub_le_max_adic v _ _
          _ ≤ max (ε * R' ^ 2) (R' * (ε * R' ^ 2)) := by
              apply max_le_max
              · rw [norm_mul]; exact mul_le_mul hx hbp (norm_nonneg _) hε0.le
              · rw [norm_mul]; exact mul_le_mul hb₂ hin' (norm_nonneg _) hR'0.le
          _ ≤ ε * R' ^ 3 := by
              apply max_le (mul_le_mul_of_nonneg_left hR'3 hε0.le)
              calc R' * (ε * R' ^ 2) = ε * R' ^ 3 := by ring
                _ ≤ ε * R' ^ 3 := le_rfl
          _ ≤ r := hεr

private theorem exists_forall_cellSectionOf_mul_lowerUnipotent3 (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (h : LocalGL3 v) (x y z : v.adicCompletion ℚ), ‖x‖ ≤ ε → ‖y‖ ≤ ε → ‖z‖ ≤ ε →
      cellSectionOf v ν Φ (h * lowerUnipotent3 x y z) = cellSectionOf v ν Φ h := by
  obtain ⟨ε, hε, hcore⟩ := exists_forall_cellSectionOf_mul_lowerUnipotent3_of_ne v ν Φ hν hΦl hΦc
  refine ⟨min ε 1, lt_min hε zero_lt_one, fun h x y z hx hy hz => ?_⟩
  have hx' : ‖x‖ ≤ ε := hx.trans (min_le_left _ _)
  have hy' : ‖y‖ ≤ ε := hy.trans (min_le_left _ _)
  have hz' : ‖z‖ ≤ ε := hz.trans (min_le_left _ _)
  by_cases hg : h ∈ bigCell3 v
  · by_cases hΦ : Φ (cellRatio v h) = 0
    ·
      have h0 : cellSectionOf v ν Φ h = 0 := by
        rw [cellSectionOf_apply_of_mem v ν Φ hg, hΦ, mul_zero]
      rw [h0]
      by_cases hg' : h * lowerUnipotent3 x y z ∈ bigCell3 v
      · by_cases hΦ' : Φ (cellRatio v (h * lowerUnipotent3 x y z)) = 0
        · rw [cellSectionOf_apply_of_mem v ν Φ hg', hΦ', mul_zero]
        · have hxy : ‖x * y - z‖ ≤ ε := by
            calc ‖x * y - z‖ ≤ max ‖x * y‖ ‖z‖ := norm_sub_le_max_adic v _ _
              _ ≤ max (ε * 1) ε := by
                  apply max_le_max _ hz'
                  rw [norm_mul]
                  exact mul_le_mul hx' (hy.trans (min_le_right _ _)) (norm_nonneg _) hε.le
              _ = ε := by rw [mul_one, max_self]
          have key := hcore (h * lowerUnipotent3 x y z) (-x) (-y) (x * y - z) (by rwa [norm_neg])
            (by rwa [norm_neg]) hxy hg' hΦ'
          rw [mul_lowerUnipotent3_mul_lowerUnipotent3_neg] at key
          rw [← key, h0]
      · exact cellSectionOf_apply_of_notMem v ν Φ hg'
    · exact hcore h x y z hx' hy' hz' hg hΦ
  ·
    rw [cellSectionOf_apply_of_notMem v ν Φ hg]
    by_cases hg' : h * lowerUnipotent3 x y z ∈ bigCell3 v
    · by_cases hΦ' : Φ (cellRatio v (h * lowerUnipotent3 x y z)) = 0
      · rw [cellSectionOf_apply_of_mem v ν Φ hg', hΦ', mul_zero]
      · have hxy : ‖x * y - z‖ ≤ ε := by
          calc ‖x * y - z‖ ≤ max ‖x * y‖ ‖z‖ := norm_sub_le_max_adic v _ _
            _ ≤ max (ε * 1) ε := by
                apply max_le_max _ hz'
                rw [norm_mul]
                exact mul_le_mul hx' (hy.trans (min_le_right _ _)) (norm_nonneg _) hε.le
            _ = ε := by rw [mul_one, max_self]
        have key := hcore (h * lowerUnipotent3 x y z) (-x) (-y) (x * y - z) (by rwa [norm_neg])
          (by rwa [norm_neg]) hxy hg' hΦ'
        rw [mul_lowerUnipotent3_mul_lowerUnipotent3_neg] at key
        rw [← key, cellSectionOf_apply_of_notMem v ν Φ hg]
    · exact cellSectionOf_apply_of_notMem v ν Φ hg'

end RightLower
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

section DualValueLocallyConstant

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem dualPoint_mul_lowerUnipotent3 (a : (v.adicCompletion ℚ)ˣ) (x t : v.adicCompletion ℚ) :
    dualPoint v a x * lowerUnipotent3 0 0 t = dualPoint v a (x - t) := by
  apply Units.ext
  have hx : ((dualPoint v a x : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x), 0,
        ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] := coe_dualPoint_mul_antidiagonal3 v a x
  have hxt : ((dualPoint v a (x - t) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * (x - t)), 0,
        ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] := coe_dualPoint_mul_antidiagonal3 v a (x - t)
  rw [Units.val_mul, lowerUnipotent3_coe, hx, hxt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem exists_forall_jacquetValue_dualTranslate_add_eq (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : (v.adicCompletion ℚ)ˣ) (x t : v.adicCompletion ℚ), ‖t‖ ≤ δ →
      jacquetValue v (dualTranslate v ν Φ a (x + t)) = jacquetValue v (dualTranslate v ν Φ a x) := by
  obtain ⟨δ, hδ, hL⟩ := exists_forall_cellSectionOf_mul_lowerUnipotent3 v ν Φ hν hΦl hΦc
  refine ⟨δ, hδ, fun a x t ht => ?_⟩
  have hfun : dualTranslate v ν Φ a (x + t) = dualTranslate v ν Φ a x := by
    funext h
    rw [dualTranslate_apply, dualTranslate_apply, show x + t = x - -t by ring, ← dualPoint_mul_lowerUnipotent3,
      ← mul_assoc]
    exact hL _ 0 0 (-t) (by simpa using hδ.le) (by simpa using hδ.le) (by rwa [norm_neg])
  rw [hfun]

end DualValueLocallyConstant
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

private def dualConj3 {A : Type*} [CommRing A] (u x : A) : GL (Fin 3) A where
  val := !![1 - u * x, 0, u; 0, 1, 0; -(x ^ 2 * u), 0, 1 + x * u]
  inv := !![1 + u * x, 0, -u; 0, 1, 0; x ^ 2 * u, 0, 1 - x * u]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

@[scoped simp] private theorem dualConj3_coe {A : Type*} [CommRing A] (u x : A) :
    ((dualConj3 u x : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1 - u * x, 0, u; 0, 1, 0; -(x ^ 2 * u), 0, 1 + x * u] :=
  rfl

section RightDiagonal

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem gl3Entry_mul_diagonal3 (h : LocalGL3 v) (w : Fin 3 → (v.adicCompletion ℚ)ˣ) (i j : Fin 3) :
    gl3Entry v (h * diagonal3 v w) i j = gl3Entry v h i j * (w j : v.adicCompletion ℚ) := by
  simp [gl3Entry, Units.val_mul, diagonal3_coe, Matrix.mul_diagonal]

private theorem cornerEntry_mul_diagonal3 (h : LocalGL3 v) (w : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    cornerEntry v (h * diagonal3 v w) = cornerEntry v h * (w 0 : v.adicCompletion ℚ) := by
  unfold cornerEntry
  exact gl3Entry_mul_diagonal3 v h w 2 0

private theorem lowerMinor_mul_diagonal3 (h : LocalGL3 v) (w : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (h * diagonal3 v w) =
      lowerMinor v h * ((w 0 : v.adicCompletion ℚ) * (w 1 : v.adicCompletion ℚ)) := by
  simp only [lowerMinor, gl3Entry_mul_diagonal3]
  ring

private theorem outerMinor_mul_diagonal3 (h : LocalGL3 v) (w : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    outerMinor v (h * diagonal3 v w) =
      outerMinor v h * ((w 0 : v.adicCompletion ℚ) * (w 2 : v.adicCompletion ℚ)) := by
  simp only [outerMinor, gl3Entry_mul_diagonal3]
  ring

private theorem gl3Det_mul_diagonal3 (h : LocalGL3 v) (w : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    gl3Det v (h * diagonal3 v w) =
      gl3Det v h * ((w 0 : v.adicCompletion ℚ) * (w 1 : v.adicCompletion ℚ) * (w 2 : v.adicCompletion ℚ)) := by
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, diagonal3_coe, Matrix.det_diagonal, Fin.prod_univ_three]

private theorem diagonal3_one : diagonal3 v (1 : Fin 3 → (v.adicCompletion ℚ)ˣ) = 1 := by
  ext i j
  simp [diagonal3_coe, Matrix.one_apply, Matrix.diagonal_apply]

private theorem mul_diagonal3_mul_diagonal3_inv (h : LocalGL3 v) (w : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    h * diagonal3 v w * diagonal3 v w⁻¹ = h := by
  rw [mul_assoc, ← diagonal3_mul, mul_inv_cancel, diagonal3_one, mul_one]

private theorem exists_forall_cellSectionOf_mul_diagonal3_of_ne (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (h : LocalGL3 v) (w : Fin 3 → (v.adicCompletion ℚ)ˣ),
      (∀ i, ‖(w i : v.adicCompletion ℚ) - 1‖ ≤ η) → h ∈ bigCell3 v → Φ (cellRatio v h) ≠ 0 →
        cellSectionOf v ν Φ (h * diagonal3 v w) = cellSectionOf v ν Φ h := by
  obtain ⟨r, hr, hrΦ⟩ := exists_invariance_radius v Φ hΦl hΦc
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  obtain ⟨k₀, hk₀⟩ := exists_forall_charExt_mul_eq v (ν 0) (hν 0)
  obtain ⟨k₁, hk₁⟩ := exists_forall_charExt_mul_eq v (ν 1) (hν 1)
  obtain ⟨k₂, hk₂⟩ := exists_forall_charExt_mul_eq v (ν 2) (hν 2)
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq_def
  have hq1 : (1 : ℝ) < q := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  set R' : ℝ := max R 1 with hR'_def
  have hR'1 : (1 : ℝ) ≤ R' := le_max_right _ _
  have hR'0 : (0 : ℝ) < R' := zero_lt_one.trans_le hR'1
  have hRR' : R ≤ R' := le_max_left _ _
  set k : ℕ := max (max k₀ k₁) (max k₂ 1) with hk_def
  have hk1 : 1 ≤ k := (le_max_right _ _).trans (le_max_right _ _)
  have hkk₀ : k₀ ≤ k := (le_max_left _ _).trans (le_max_left _ _)
  have hkk₁ : k₁ ≤ k := (le_max_right _ _).trans (le_max_left _ _)
  have hkk₂ : k₂ ≤ k := (le_max_left _ _).trans (le_max_right _ _)
  set η : ℝ := min (q ^ (-(k : ℤ))) (r / R') with hη_def
  have hη0 : 0 < η := lt_min (zpow_pos hq0 _) (div_pos hr hR'0)
  have hηk : η ≤ q ^ (-(k : ℤ)) := min_le_left _ _
  have hηr : η * R' ≤ r := by
    calc η * R' ≤ r / R' * R' := by gcongr; exact min_le_right _ _
      _ = r := div_mul_cancel₀ r hR'0.ne'
  refine ⟨η, hη0, fun h w hw hg hΦ => ?_⟩
  obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v h).mp hg
  have hmono : ∀ {k' : ℕ}, k' ≤ k → WithZero.exp (-(k : ℤ)) ≤ WithZero.exp (-(k' : ℤ)) := fun hk' =>
    WithZero.exp_le_exp.mpr (neg_le_neg (Int.ofNat_le.mpr hk'))

  have hv : ∀ i, Valued.v ((w i : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)) := fun i =>
    valued_le_of_norm_le_zpow v ((hw i).trans hηk)
  have hv1 : ∀ i, Valued.v (w i : v.adicCompletion ℚ) = 1 := fun i =>
    valued_eq_one_of_valued_sub_one_le v hk1 (hv i)
  have hn1 : ∀ i, ‖(w i : v.adicCompletion ℚ)‖ = 1 := fun i => norm_eq_one_of_valued_eq_one v (hv1 i)
  have hw0 : ∀ i, (w i : v.adicCompletion ℚ) ≠ 0 := fun i => (w i).ne_zero
  set c := cornerEntry v h with hc_def
  set ℓ := lowerMinor v h with hℓ_def
  set o := outerMinor v h with ho_def
  set D := gl3Det v h with hD_def
  have hc' : cornerEntry v (h * diagonal3 v w) = c * w 0 := cornerEntry_mul_diagonal3 v h w
  have hℓ' : lowerMinor v (h * diagonal3 v w) = ℓ * (w 0 * w 1) := lowerMinor_mul_diagonal3 v h w
  have ho' : outerMinor v (h * diagonal3 v w) = o * (w 0 * w 2) := outerMinor_mul_diagonal3 v h w
  have hD' : gl3Det v (h * diagonal3 v w) = D * (w 0 * w 1 * w 2) := gl3Det_mul_diagonal3 v h w
  have hg' : h * diagonal3 v w ∈ bigCell3 v := by
    rw [mem_bigCell3_iff, hc', hℓ']
    exact ⟨mul_ne_zero hc (hw0 0), mul_ne_zero hl (mul_ne_zero (hw0 0) (hw0 1))⟩
  rw [cellSectionOf_apply_of_mem v ν Φ hg', cellSectionOf_apply_of_mem v ν Φ hg]
  congr 1
  · rw [cellValue, cellValue, hc', hℓ', hD', ← hc_def, ← hℓ_def, ← hD_def]
    have e0 : charExt (ν 0) (D * (w 0 * w 1 * w 2) / (ℓ * (w 0 * w 1))) = charExt (ν 0) (D / ℓ) := by
      rw [show D * (w 0 * w 1 * w 2) / (ℓ * (w 0 * w 1)) = (w 2 : v.adicCompletion ℚ) * (D / ℓ) by
        field_simp]
      exact hk₀ _ _ ((hv 2).trans (hmono hkk₀))
    have e1 : charExt (ν 1) (ℓ * (w 0 * w 1) / (c * w 0)) = charExt (ν 1) (ℓ / c) := by
      rw [show ℓ * (w 0 * w 1) / (c * w 0) = (w 1 : v.adicCompletion ℚ) * (ℓ / c) by field_simp]
      exact hk₁ _ _ ((hv 1).trans (hmono hkk₁))
    have e2 : charExt (ν 2) (c * w 0) = charExt (ν 2) c := by
      rw [mul_comm]
      exact hk₂ _ _ ((hv 0).trans (hmono hkk₂))
    have en : (‖D * (w 0 * w 1 * w 2) / (ℓ * (w 0 * w 1))‖ / ‖c * (w 0 : v.adicCompletion ℚ)‖ : ℝ) =
        ‖D / ℓ‖ / ‖c‖ := by
      simp only [norm_div, norm_mul, hn1, mul_one]
    rw [e0, e1, e2, en]
  · apply hrΦ
    have hb : ∀ i, ‖cellRatio v h i‖ ≤ R' := fun i => (hR _ hΦ i).trans hRR'
    have hd : ∀ i j, ‖(((w i : v.adicCompletion ℚ) - 1) - ((w j : v.adicCompletion ℚ) - 1)) / w j‖ ≤ η := by
      intro i j
      rw [norm_div, hn1, div_one]
      exact (norm_sub_le_max_adic v _ _).trans (max_le (hw i) (hw j))
    have hfin : ∀ (i j m : Fin 3),
        ‖cellRatio v h m * ((((w i : v.adicCompletion ℚ) - 1) - ((w j : v.adicCompletion ℚ) - 1)) / w j)‖ ≤ r := by
      intro i j m
      rw [norm_mul]
      calc ‖cellRatio v h m‖ * ‖(((w i : v.adicCompletion ℚ) - 1) - ((w j : v.adicCompletion ℚ) - 1)) / w j‖
            ≤ R' * η := mul_le_mul (hb m) (hd i j) (norm_nonneg _) hR'0.le
        _ = η * R' := mul_comm _ _
        _ ≤ r := hηr
    have hw00 := hw0 0
    have hw01 := hw0 1
    have hw02 := hw0 2
    intro i
    match i with
    | 0 =>
        have e : cellRatio v (h * diagonal3 v w) 0 - cellRatio v h 0 =
            cellRatio v h 0 * ((((w 1 : v.adicCompletion ℚ) - 1) - ((w 0 : v.adicCompletion ℚ) - 1)) / w 0) := by
          rw [cellRatio_apply_zero, cellRatio_apply_zero, gl3Entry_mul_diagonal3, hc', ← hc_def]
          field_simp
          ring
        rw [e]
        exact hfin 1 0 0
    | 1 =>
        have e : cellRatio v (h * diagonal3 v w) 1 - cellRatio v h 1 =
            cellRatio v h 1 * ((((w 2 : v.adicCompletion ℚ) - 1) - ((w 0 : v.adicCompletion ℚ) - 1)) / w 0) := by
          rw [cellRatio_apply_one, cellRatio_apply_one, gl3Entry_mul_diagonal3, hc', ← hc_def]
          field_simp
          ring
        rw [e]
        exact hfin 2 0 1
    | 2 =>
        have e : cellRatio v (h * diagonal3 v w) 2 - cellRatio v h 2 =
            cellRatio v h 2 * ((((w 2 : v.adicCompletion ℚ) - 1) - ((w 1 : v.adicCompletion ℚ) - 1)) / w 1) := by
          rw [cellRatio_apply_two, cellRatio_apply_two, ho', hℓ', ← ho_def, ← hℓ_def]
          field_simp
          ring
        rw [e]
        exact hfin 2 1 2

private theorem exists_forall_cellSectionOf_mul_diagonal3 (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (h : LocalGL3 v) (w : Fin 3 → (v.adicCompletion ℚ)ˣ),
      (∀ i, ‖(w i : v.adicCompletion ℚ) - 1‖ ≤ η) →
        cellSectionOf v ν Φ (h * diagonal3 v w) = cellSectionOf v ν Φ h := by
  obtain ⟨η, hη, hcore⟩ := exists_forall_cellSectionOf_mul_diagonal3_of_ne v ν Φ hν hΦl hΦc
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq_def
  have hq1 : (1 : ℝ) < q := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1

  refine ⟨min η (q ^ (-(1 : ℤ))), lt_min hη (zpow_pos hq0 _), fun h w hw => ?_⟩
  have hw' : ∀ i, ‖(w i : v.adicCompletion ℚ) - 1‖ ≤ η := fun i => (hw i).trans (min_le_left _ _)
  have hn1 : ∀ i, ‖(w i : v.adicCompletion ℚ)‖ = 1 := fun i =>
    norm_eq_one_of_valued_eq_one v (valued_eq_one_of_valued_sub_one_le v le_rfl
      (valued_le_of_norm_le_zpow v (by simpa using (hw i).trans (min_le_right _ _))))
  have hwinv : ∀ i, ‖((w⁻¹ : Fin 3 → (v.adicCompletion ℚ)ˣ) i : v.adicCompletion ℚ) - 1‖ ≤ η := by
    intro i
    have h1 : ((w⁻¹ : Fin 3 → (v.adicCompletion ℚ)ˣ) i : v.adicCompletion ℚ) - 1 =
        -(((w i : v.adicCompletion ℚ) - 1) / (w i : v.adicCompletion ℚ)) := by
      rw [Pi.inv_apply, Units.val_inv_eq_inv_val]
      field_simp [(w i).ne_zero]
      ring
    rw [h1, norm_neg, norm_div, hn1, div_one]
    exact hw' i
  by_cases hg : h ∈ bigCell3 v
  · by_cases hΦ : Φ (cellRatio v h) = 0
    · have h0 : cellSectionOf v ν Φ h = 0 := by rw [cellSectionOf_apply_of_mem v ν Φ hg, hΦ, mul_zero]
      rw [h0]
      by_cases hg' : h * diagonal3 v w ∈ bigCell3 v
      · by_cases hΦ' : Φ (cellRatio v (h * diagonal3 v w)) = 0
        · rw [cellSectionOf_apply_of_mem v ν Φ hg', hΦ', mul_zero]
        · have key := hcore (h * diagonal3 v w) w⁻¹ hwinv hg' hΦ'
          rw [mul_diagonal3_mul_diagonal3_inv] at key
          rw [← key, h0]
      · exact cellSectionOf_apply_of_notMem v ν Φ hg'
    · exact hcore h w hw' hg hΦ
  · rw [cellSectionOf_apply_of_notMem v ν Φ hg]
    by_cases hg' : h * diagonal3 v w ∈ bigCell3 v
    · by_cases hΦ' : Φ (cellRatio v (h * diagonal3 v w)) = 0
      · rw [cellSectionOf_apply_of_mem v ν Φ hg', hΦ', mul_zero]
      · have key := hcore (h * diagonal3 v w) w⁻¹ hwinv hg' hΦ'
        rw [mul_diagonal3_mul_diagonal3_inv] at key
        rw [← key, cellSectionOf_apply_of_notMem v ν Φ hg]
    · exact cellSectionOf_apply_of_notMem v ν Φ hg'

end RightDiagonal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"

section Shear

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def jacquetShear (e : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) ≃ᵐ
      (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  exact
    { toFun := fun p => (p.1, p.2.1 + e, p.2.2 + p.1 * e)
      invFun := fun p => (p.1, p.2.1 - e, p.2.2 - p.1 * e)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp
      measurable_toFun :=
        (continuous_fst.prodMk ((continuous_snd.fst.add continuous_const).prodMk
          (continuous_snd.snd.add (continuous_fst.mul continuous_const)))).measurable
      measurable_invFun :=
        (continuous_fst.prodMk ((continuous_snd.fst.sub continuous_const).prodMk
          (continuous_snd.snd.sub (continuous_fst.mul continuous_const)))).measurable }

private theorem jacquetShear_apply (e : v.adicCompletion ℚ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    jacquetShear v e p = (p.1, p.2.1 + e, p.2.2 + p.1 * e) :=
  rfl

private theorem measurePreserving_jacquetShear (e : v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    MeasurePreserving (jacquetShear v e) (jacquetHaar3 v) (jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI := sFinite_selfDualHaarAt ℚ v
  have hshape : (jacquetShear v e : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ →
      v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) =
      fun p => (id p.1, (fun (a : v.adicCompletion ℚ) (q : v.adicCompletion ℚ × v.adicCompletion ℚ) =>
        q + (e, a * e)) p.1 p.2) := by
    funext p
    rw [jacquetShear_apply]
    ext <;> simp
  unfold jacquetHaar3
  rw [hshape]
  refine MeasurePreserving.skew_product (μa := selfDualHaarAt ℚ v) (μb := selfDualHaarAt ℚ v)
    (μc := (selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) (μd := (selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))
    (g := fun (a : v.adicCompletion ℚ) (q : v.adicCompletion ℚ × v.adicCompletion ℚ) => q + (e, a * e))
    (MeasurePreserving.id (selfDualHaarAt ℚ v)) ?_ (Filter.Eventually.of_forall fun a => ?_)
  · exact (continuous_snd.add ((continuous_const.prodMk (continuous_fst.mul continuous_const)))).measurable
  · exact map_add_right_eq_self _ _

private theorem preimage_jacquetShear_unipotentBall3
    {c : ℤ} {e : v.adicCompletion ℚ} (he : Valued.v e ≤ WithZero.exp c) :
    jacquetShear v e ⁻¹' unipotentBall3 v c = unipotentBall3 v c := by
  have he' : Valued.v (-e) ≤ WithZero.exp c := by rwa [Valuation.map_neg]
  ext p
  simp only [Set.mem_preimage, jacquetShear_apply, mem_unipotentBall3_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [show p.2.1 = (p.2.1 + e) + -e by ring]
      exact (Valuation.map_add _ _ _).trans (max_le h2 he')
    · rw [show p.2.2 = (p.2.2 + p.1 * e) + p.1 * -e by ring]
      refine (Valuation.map_add _ _ _).trans (max_le h3 ?_)
      rw [Valuation.map_mul, two_mul, WithZero.exp_add]
      exact mul_le_mul' h1 he'
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, (Valuation.map_add _ _ _).trans (max_le h2 he), ?_⟩
    refine (Valuation.map_add _ _ _).trans (max_le h3 ?_)
    rw [Valuation.map_mul, two_mul, WithZero.exp_add]
    exact mul_le_mul' h1 he

private theorem jacquetValue_rightTranslate_upperUnipotent3_mid_mul (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (g : LocalGL3 v) (e : v.adicCompletion ℚ) :
    jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 0 e 0 * g) (cellSectionOf v ν Φ)) =
      psiLocal ℚ v e * jacquetValue v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ)) := by
  letI := localBorel ℚ v
  set f₁ := gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 0 e 0 * g) (cellSectionOf v ν Φ) with hf₁
  set f₀ := gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ) with hf₀
  obtain ⟨c₁, h₁⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩
    (upperUnipotent3 0 e 0 * g)
  obtain ⟨c₀, h₀⟩ := exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v ν hν Φ ⟨hΦl, hΦc⟩ g
  obtain ⟨N, hN⟩ := exists_nat_valued_le_exp v e
  set c : ℤ := max (max (c₁ : ℤ) (c₀ : ℤ)) (N : ℤ) with hc_def
  have hc₁ : (c₁ : ℤ) ≤ c := (le_max_left _ _).trans (le_max_left _ _)
  have hc₀ : (c₀ : ℤ) ≤ c := (le_max_right _ _).trans (le_max_left _ _)
  have hcN : (N : ℤ) ≤ c := le_max_right _ _
  have hst₁ : ∃ c' : ℕ, ∀ c : ℤ, (c' : ℤ) ≤ c → jacquetTruncated3 v c f₁ = jacquetTruncated3 v c' f₁ :=
    ⟨c₁, fun c hc => (h₁ c hc).2⟩
  have hst₀ : ∃ c' : ℕ, ∀ c : ℤ, (c' : ℤ) ≤ c → jacquetTruncated3 v c f₀ = jacquetTruncated3 v c' f₀ :=
    ⟨c₀, fun c hc => (h₀ c hc).2⟩
  have hlev₁ : (jacquetLevel v f₁ : ℤ) ≤ c :=
    (Int.ofNat_le.mpr (jacquetLevel_le v f₁ fun c hc => (h₁ c hc).2)).trans hc₁
  have hlev₀ : (jacquetLevel v f₀ : ℤ) ≤ c :=
    (Int.ofNat_le.mpr (jacquetLevel_le v f₀ fun c hc => (h₀ c hc).2)).trans hc₀
  rw [← jacquetTruncated3_eq_jacquetValue v f₁ hst₁ hlev₁, ← jacquetTruncated3_eq_jacquetValue v f₀ hst₀ hlev₀]
  have he : Valued.v e ≤ WithZero.exp c := hN.trans (WithZero.exp_le_exp.mpr hcN)
  set G : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ :=
    fun p => psiLocal ℚ v (-(p.1 + p.2.1)) * f₀ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) with hG
  have hint : ∀ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
      psiLocal ℚ v (-(p.1 + p.2.1)) * f₁ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) =
        psiLocal ℚ v e * G (jacquetShear v e p) := by
    intro p
    simp only [hG, hf₁, hf₀, gl3AmbientRightTranslate_apply, jacquetShear_apply]
    rw [show antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * (upperUnipotent3 0 e 0 * g) =
        antidiagonal3 v * upperUnipotent3 p.1 (p.2.1 + e) (p.2.2 + p.1 * e) * g by
      rw [← mul_assoc, mul_assoc (antidiagonal3 v), upperUnipotent3_mul_upperUnipotent3, add_zero, add_zero]]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  unfold jacquetTruncated3
  simp_rw [hint]
  rw [integral_const_mul]
  congr 1
  have key := (measurePreserving_jacquetShear v e).setIntegral_preimage_emb
    (jacquetShear v e).measurableEmbedding G (unipotentBall3 v c)
  rw [preimage_jacquetShear_unipotentBall3 v he] at key
  exact key

end Shear
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"

section DualValueLargeModule

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem dualPoint_mul_dualConj3 (a : (v.adicCompletion ℚ)ˣ) (x u : v.adicCompletion ℚ) :
    dualPoint v a x * dualConj3 u x = upperUnipotent3 0 (u * a) 0 * dualPoint v a x := by
  apply Units.ext
  have hx : ((dualPoint v a x : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x), 0,
        ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] := coe_dualPoint_mul_antidiagonal3 v a x
  have ha : (a : v.adicCompletion ℚ) ≠ 0 := a.ne_zero
  rw [Units.val_mul, Units.val_mul, dualConj3_coe, upperUnipotent3_coe, hx]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    <;> first | ring1 | (field_simp; ring1)

private theorem diagonal3_mk0_coe (A : v.adicCompletion ℚ) (hA : A ≠ 0) :
    ((diagonal3 v ![Units.mk0 A hA, 1, (Units.mk0 A hA)⁻¹] : LocalGL3 v) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = !![A, 0, 0; 0, 1, 0; 0, 0, A⁻¹] := by
  rw [diagonal3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem dualConj3_eq_mul (u x : v.adicCompletion ℚ) (hA : 1 - u * x ≠ 0) :
    dualConj3 u x = lowerUnipotent3 0 0 (-(x ^ 2 * u) / (1 - u * x)) *
      diagonal3 v ![Units.mk0 (1 - u * x) hA, 1, (Units.mk0 (1 - u * x) hA)⁻¹] *
        upperUnipotent3 0 0 (u / (1 - u * x)) := by
  have hA' : 1 - x * u ≠ 0 := by rwa [mul_comm] at hA
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dualConj3_coe, lowerUnipotent3_coe, diagonal3_mk0_coe, upperUnipotent3_coe]

  have h1 : (!![(1 : v.adicCompletion ℚ) - u * x, 0, 0; 0, 1, 0; 0, 0, (1 - u * x)⁻¹] *
      !![(1 : v.adicCompletion ℚ), 0, u / (1 - u * x); 0, 1, 0; 0, 0, 1]) =
        !![1 - u * x, 0, u; 0, 1, 0; 0, 0, (1 - u * x)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    field_simp
  rw [Matrix.mul_assoc, h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    <;> first | ring1 | (field_simp; ring1) | field_simp

private theorem exists_forall_jacquetValue_dualTranslate_eq_zero_of_lt_norm (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      C * max 1 (‖x‖ ^ 2) < ‖(a : v.adicCompletion ℚ)‖ → jacquetValue v (dualTranslate v ν Φ a x) = 0 := by
  obtain ⟨εU, hεU, hU⟩ := exists_forall_cellSectionOf_mul_upperUnipotent3 v ν Φ hΦl hΦc
  obtain ⟨εL, hεL, hL⟩ := exists_forall_cellSectionOf_mul_lowerUnipotent3 v ν Φ hν hΦl hΦc
  obtain ⟨η, hη, hD⟩ := exists_forall_cellSectionOf_mul_diagonal3 v ν Φ hν hΦl hΦc
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : v.adicCompletion ℚ, psiLocal ℚ v w₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact psiLocal_ne_one ℚ v (AddChar.ext _ _ h)
  set ε₀ : ℝ := min (min εU εL) (min η (1 / 2)) with hε₀_def
  have hε₀0 : 0 < ε₀ := lt_min (lt_min hεU hεL) (lt_min hη one_half_pos)
  have hε₀U : ε₀ ≤ εU := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀L : ε₀ ≤ εL := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀η : ε₀ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀h : ε₀ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨‖w₀‖ / ε₀, div_nonneg (norm_nonneg _) hε₀0.le, fun a x hax => ?_⟩
  set M : ℝ := max 1 (‖x‖ ^ 2) with hM_def
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := zero_lt_one.trans_le hM1
  have hxM : ‖x‖ ≤ M := by
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hx1.trans hM1
    · push Not at hx1
      calc ‖x‖ = ‖x‖ ^ 1 := (pow_one _).symm
        _ ≤ ‖x‖ ^ 2 := pow_le_pow_right₀ hx1.le (by norm_num)
        _ ≤ M := le_max_right _ _
  have hx2M : ‖x‖ ^ 2 ≤ M := le_max_right _ _
  have hapos : 0 < ‖(a : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr a.ne_zero

  set u : v.adicCompletion ℚ := w₀ / a with hu_def
  have hua : u * a = w₀ := div_mul_cancel₀ w₀ a.ne_zero
  have huM : ‖u‖ * M ≤ ε₀ := by
    rw [hu_def, norm_div, div_mul_eq_mul_div, div_le_iff₀ hapos]
    have h1 : ‖w₀‖ / ε₀ * M < ‖(a : v.adicCompletion ℚ)‖ := hax
    rw [div_mul_eq_mul_div, div_lt_iff₀ hε₀0] at h1
    linarith [mul_comm ε₀ ‖(a : v.adicCompletion ℚ)‖]
  have hu1 : ‖u‖ ≤ ε₀ := by
    calc ‖u‖ = ‖u‖ * 1 := (mul_one _).symm
      _ ≤ ‖u‖ * M := by gcongr
      _ ≤ ε₀ := huM
  have hux : ‖u * x‖ ≤ ε₀ := by
    rw [norm_mul]
    calc ‖u‖ * ‖x‖ ≤ ‖u‖ * M := by gcongr
      _ ≤ ε₀ := huM
  have hux2 : ‖x ^ 2 * u‖ ≤ ε₀ := by
    rw [norm_mul, norm_pow, mul_comm]
    calc ‖u‖ * ‖x‖ ^ 2 ≤ ‖u‖ * M := by gcongr
      _ ≤ ε₀ := huM

  have hux1 : ‖u * x‖ < 1 := hux.trans_lt (hε₀h.trans_lt (by norm_num))
  have hAn : ‖1 - u * x‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_one, norm_neg,
      max_eq_left hux1.le]
    rw [norm_one, norm_neg]
    exact (ne_of_gt hux1)
  have hA : 1 - u * x ≠ 0 := fun h0 => by simp [h0] at hAn

  have hfU : ‖u / (1 - u * x)‖ ≤ εU := by rw [norm_div, hAn, div_one]; exact hu1.trans hε₀U
  have hfL : ‖-(x ^ 2 * u) / (1 - u * x)‖ ≤ εL := by rw [norm_div, norm_neg, hAn, div_one]; exact hux2.trans hε₀L
  have hfD : ∀ i, ‖((![Units.mk0 (1 - u * x) hA, 1, (Units.mk0 (1 - u * x) hA)⁻¹] :
      Fin 3 → (v.adicCompletion ℚ)ˣ) i : v.adicCompletion ℚ) - 1‖ ≤ η := by
    intro i
    match i with
    | 0 =>
        change ‖((Units.mk0 (1 - u * x) hA : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1‖ ≤ η
        rw [Units.val_mk0, show (1 : v.adicCompletion ℚ) - u * x - 1 = -(u * x) by ring, norm_neg]
        exact hux.trans hε₀η
    | 1 =>
        change ‖((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1‖ ≤ η
        rw [Units.val_one, sub_self, norm_zero]
        exact hη.le
    | 2 =>
        change ‖(((Units.mk0 (1 - u * x) hA)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1‖ ≤ η
        rw [Units.val_inv_eq_inv_val, Units.val_mk0,
          show ((1 : v.adicCompletion ℚ) - u * x)⁻¹ - 1 = (u * x) / (1 - u * x) by field_simp; ring, norm_div, hAn,
          div_one]
        exact hux.trans hε₀η

  set g := dualPoint v a x with hg_def
  have hfun : gl3AmbientRightTranslate (R := ℂ) (g * dualConj3 u x) (cellSectionOf v ν Φ) =
      gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ) := by
    funext h
    rw [gl3AmbientRightTranslate_apply, gl3AmbientRightTranslate_apply, dualConj3_eq_mul v u x hA, ← mul_assoc,
      ← mul_assoc, ← mul_assoc, hU _ 0 0 _ (by simpa using hεU.le) (by simpa using hεU.le) hfU, hD _ _ hfD,
      hL _ 0 0 _ (by simpa using hεL.le) (by simpa using hεL.le) hfL]

  have h2 := jacquetValue_rightTranslate_upperUnipotent3_mid_mul v ν Φ hν hΦl hΦc g (u * a)
  rw [← dualPoint_mul_dualConj3, hfun, hua] at h2
  have h3 : jacquetValue v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ)) =
      jacquetValue v (dualTranslate v ν Φ a x) := rfl
  rw [h3] at h2
  have h4 : (1 - psiLocal ℚ v w₀) * jacquetValue v (dualTranslate v ν Φ a x) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd (sub_eq_zero.mp h5).symm hw₀
  · exact h5

private theorem exists_forall_lt_norm_forall_jacquetValue_dualTranslate_eq_zero (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ A₁ : ℝ, ∀ (a : (v.adicCompletion ℚ)ˣ), A₁ < ‖(a : v.adicCompletion ℚ)‖ →
      ∀ x : v.adicCompletion ℚ, jacquetValue v (dualTranslate v ν Φ a x) = 0 := by
  obtain ⟨X₀, hX₀⟩ := exists_forall_lt_norm_jacquetValue_dualTranslate_eq_zero v ν Φ hν hΦl hΦc
  obtain ⟨C, hC, hCa⟩ := exists_forall_jacquetValue_dualTranslate_eq_zero_of_lt_norm v ν Φ hν hΦl hΦc
  refine ⟨C * max 1 (X₀ ^ 2), fun a ha x => ?_⟩
  by_cases hx : X₀ < ‖x‖
  · exact hX₀ a x hx
  · push Not at hx
    apply hCa a x
    calc C * max 1 (‖x‖ ^ 2) ≤ C * max 1 (X₀ ^ 2) :=
          mul_le_mul_of_nonneg_left (max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hx 2)) hC
      _ < ‖(a : v.adicCompletion ℚ)‖ := ha

end DualValueLargeModule
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

open Classical in

private noncomputable def dualSlice (x t : v.adicCompletion ℚ) : ℂ :=
  if h : t = 0 then 0 else
    jacquetValue v (dualTranslate v ν Φ (Units.mk0 t h) x) * ((modulus t : ℝ) : ℂ)⁻¹

private theorem dualSlice_zero (x : v.adicCompletion ℚ) : dualSlice v ν Φ x 0 = 0 := by
  simp [dualSlice]
end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section DualFnOffZero

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem norm_eq_one_of_norm_sub_one_lt_one_adic {w : v.adicCompletion ℚ} (hw : ‖w - 1‖ < 1) : ‖w‖ = 1 := by
  have h : ‖w - 1‖ ≠ ‖(1 : v.adicCompletion ℚ)‖ := by
    rw [norm_one]
    exact hw.ne
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h
  rw [sub_add_cancel, norm_one, max_eq_right hw.le] at this
  exact this

private theorem diagonal3_one_one_coe (w : (v.adicCompletion ℚ)ˣ) :
    ((diagonal3 v ![1, 1, w] : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, 0, 0; 0, 1, 0; 0, 0, (w : v.adicCompletion ℚ)] := by
  rw [diagonal3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem coe_dualPoint (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    ((dualPoint v a x : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 1, 0, 0; -(((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x), 0,
        ((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] :=
  coe_dualPoint_mul_antidiagonal3 v a x

private theorem dualPoint_mul (a w : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    dualPoint v (a * w) x =
      dualPoint v a x * diagonal3 v ![1, 1, w⁻¹] * lowerUnipotent3 0 0 (x * ((w : v.adicCompletion ℚ) - 1)) := by
  have ha : (a : v.adicCompletion ℚ) ≠ 0 := a.ne_zero
  have hw : (w : v.adicCompletion ℚ) ≠ 0 := w.ne_zero
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_dualPoint, coe_dualPoint, diagonal3_one_one_coe, lowerUnipotent3_coe]
  simp only [Units.val_inv_eq_inv_val, Units.val_mul]
  have h1 : (!![(0 : v.adicCompletion ℚ), 1, 0; 1, 0, 0; -((a : v.adicCompletion ℚ)⁻¹ * x), 0,
        (a : v.adicCompletion ℚ)⁻¹] *
      !![(1 : v.adicCompletion ℚ), 0, 0; 0, 1, 0; 0, 0, (w : v.adicCompletion ℚ)⁻¹]) =
        !![0, 1, 0; 1, 0, 0; -((a : v.adicCompletion ℚ)⁻¹ * x), 0,
          (a : v.adicCompletion ℚ)⁻¹ * (w : v.adicCompletion ℚ)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  rw [h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    <;> first | ring1 | (field_simp; ring1)

private theorem exists_forall_dualTranslate_mul_eq (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (a w : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      ‖(w : v.adicCompletion ℚ) - 1‖ ≤ η → ‖x * ((w : v.adicCompletion ℚ) - 1)‖ ≤ η →
        dualTranslate v ν Φ (a * w) x = dualTranslate v ν Φ a x := by
  obtain ⟨ηD, hηD0, hD⟩ := exists_forall_cellSectionOf_mul_diagonal3 v ν Φ hν hΦl hΦc
  obtain ⟨ε, hε0, hL⟩ := exists_forall_cellSectionOf_mul_lowerUnipotent3 v ν Φ hν hΦl hΦc
  refine ⟨min (min ηD ε) (1 / 2), by positivity, fun a w x hw hxw => ?_⟩
  have hwD : ‖(w : v.adicCompletion ℚ) - 1‖ ≤ ηD := hw.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hxε : ‖x * ((w : v.adicCompletion ℚ) - 1)‖ ≤ ε := hxw.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hw1 : ‖(w : v.adicCompletion ℚ) - 1‖ < 1 :=
    (hw.trans (min_le_right _ _)).trans_lt (by norm_num)
  have hwn : ‖(w : v.adicCompletion ℚ)‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one_adic v hw1
  have hwinv : ‖(w : v.adicCompletion ℚ)⁻¹ - 1‖ = ‖(w : v.adicCompletion ℚ) - 1‖ := by
    have hw0 : (w : v.adicCompletion ℚ) ≠ 0 := w.ne_zero
    rw [show (w : v.adicCompletion ℚ)⁻¹ - 1 = (w : v.adicCompletion ℚ)⁻¹ * (1 - w) by
        rw [mul_sub, mul_one, inv_mul_cancel₀ hw0],
      norm_mul, norm_inv, hwn, inv_one, one_mul, norm_sub_rev]
  funext h
  rw [dualTranslate_apply, dualTranslate_apply, dualPoint_mul, ← mul_assoc, ← mul_assoc,
    hL _ 0 0 _ (by simpa using hε0.le) (by simpa using hε0.le) hxε, hD _ _ fun i => ?_]
  match i with
  | 0 => simpa using hηD0.le
  | 1 => simpa using hηD0.le
  | 2 => simpa [Units.val_inv_eq_inv_val, hwinv] using hwD

private theorem exists_forall_jacquetValue_dualTranslate_mul_eq (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (a w : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      ‖(w : v.adicCompletion ℚ) - 1‖ ≤ η →
        jacquetValue v (dualTranslate v ν Φ (a * w) x) = jacquetValue v (dualTranslate v ν Φ a x) := by
  obtain ⟨X₀, hX₀⟩ := exists_forall_lt_norm_jacquetValue_dualTranslate_eq_zero v ν Φ hν hΦl hΦc
  obtain ⟨η, hη0, hη⟩ := exists_forall_dualTranslate_mul_eq v ν Φ hν hΦl hΦc
  refine ⟨min η (η / max X₀ 1), by positivity, fun a w x hw => ?_⟩
  rcases le_or_gt ‖x‖ X₀ with hx | hx
  · have hM : (0 : ℝ) < max X₀ 1 := lt_max_of_lt_right zero_lt_one
    refine congrArg (jacquetValue v) (hη a w x (hw.trans (min_le_left _ _)) ?_)
    calc ‖x * ((w : v.adicCompletion ℚ) - 1)‖ = ‖x‖ * ‖(w : v.adicCompletion ℚ) - 1‖ := norm_mul _ _
      _ ≤ max X₀ 1 * (η / max X₀ 1) :=
          mul_le_mul (hx.trans (le_max_left _ _)) (hw.trans (min_le_right _ _)) (norm_nonneg _) hM.le
      _ = η := by field_simp
  · rw [hX₀ (a * w) x hx, hX₀ a x hx]

private theorem exists_forall_dualSlice_eq_zero_of_lt (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ B : ℝ, ∀ (x t : v.adicCompletion ℚ), B < (modulus t : ℝ) → dualSlice v ν Φ x t = 0 := by
  obtain ⟨A₁, hA₁⟩ := exists_forall_lt_norm_forall_jacquetValue_dualTranslate_eq_zero v ν Φ hν hΦl hΦc
  refine ⟨A₁, fun x t ht => ?_⟩
  by_cases h0 : t = 0
  · rw [h0, dualSlice_zero]
  · have ha : A₁ < ‖((Units.mk0 t h0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ := by
      rwa [Units.val_mk0, ← modulus_real_eq_norm]
    simp only [dualSlice, dif_neg h0]
    rw [hA₁ _ ha x, zero_mul]

private theorem exists_forall_mk0_eq_mul_of_norm_sub_lt {η : ℝ} (hη : 0 < η) {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    ∀ᶠ t' in nhds t, ∃ h' : t' ≠ 0, ∃ u : (v.adicCompletion ℚ)ˣ,
      ‖(u : v.adicCompletion ℚ) - 1‖ ≤ η ∧ Units.mk0 t' h' = Units.mk0 t ht * u ∧
        (modulus t' : ℝ) = (modulus t : ℝ) := by
  have htn : (0 : ℝ) < ‖t‖ := norm_pos_iff.mpr ht
  have hρ : (0 : ℝ) < min η (1 / 2) * ‖t‖ := mul_pos (by positivity) htn
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds t hρ) fun t' ht' => ?_
  rw [Metric.mem_ball, dist_eq_norm] at ht'
  have hq : ‖t' - t‖ / ‖t‖ < min η (1 / 2) := (div_lt_iff₀ htn).mpr ht'
  have ht'0 : t' ≠ 0 := by
    rintro rfl
    rw [zero_sub, norm_neg] at hq
    rw [div_self htn.ne'] at hq
    linarith [min_le_right η (1 / 2 : ℝ)]
  set u : (v.adicCompletion ℚ)ˣ := Units.mk0 (t' / t) (div_ne_zero ht'0 ht) with hu_def
  have hu_sub : (u : v.adicCompletion ℚ) - 1 = (t' - t) / t := by
    rw [hu_def, Units.val_mk0]
    field_simp
  have hu_norm : ‖(u : v.adicCompletion ℚ) - 1‖ < min η (1 / 2) := by
    rwa [hu_sub, norm_div]
  have hun : ‖(u : v.adicCompletion ℚ)‖ = 1 :=
    norm_eq_one_of_norm_sub_one_lt_one_adic v (hu_norm.trans_le ((min_le_right _ _).trans (by norm_num)))
  have ht'eq : t' = t * u := by
    rw [hu_def, Units.val_mk0]
    field_simp
  refine ⟨ht'0, u, (hu_norm.le.trans (min_le_left _ _)), ?_, ?_⟩
  · ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, ht'eq]
  · rw [modulus_real_eq_norm, modulus_real_eq_norm, ht'eq, norm_mul, hun, mul_one]

private theorem eventually_dualSlice_eq (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (x : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    ∀ᶠ t' in nhds t, dualSlice v ν Φ x t' = dualSlice v ν Φ x t := by
  obtain ⟨η, hη0, hη⟩ := exists_forall_jacquetValue_dualTranslate_mul_eq v ν Φ hν hΦl hΦc
  filter_upwards [exists_forall_mk0_eq_mul_of_norm_sub_lt v hη0 ht] with t' ht'
  obtain ⟨ht'0, u, hu, hmk, hmod⟩ := ht'
  simp only [dualSlice, dif_neg ht, dif_neg ht'0]
  rw [hmk, hη _ u x hu, hmod]

private theorem eventually_dualFn_eq' (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (t : v.adicCompletion ℚ) (ht : t ≠ 0) :
    ∀ᶠ t' in nhds t, dualFn v ν Φ t' = dualFn v ν Φ t := by
  obtain ⟨η, hη0, hη⟩ := exists_forall_jacquetValue_dualTranslate_mul_eq v ν Φ hν hΦl hΦc
  filter_upwards [exists_forall_mk0_eq_mul_of_norm_sub_lt v hη0 ht] with t' ht'
  obtain ⟨ht'0, u, hu, hmk, hmod⟩ := ht'
  have hint : (∫ x, jacquetValue v (dualTranslate v ν Φ (Units.mk0 t ht * u) x) ∂(selfDualHaarAt ℚ v)) =
      ∫ x, jacquetValue v (dualTranslate v ν Φ (Units.mk0 t ht) x) ∂(selfDualHaarAt ℚ v) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => hη _ u x hu)
  simp only [dualFn, dif_neg ht, dif_neg ht'0]
  rw [hmk, hmod, hint]

end DualFnOffZero
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section DualNet

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem isCompact_setOf_norm_le (X : ℝ) : IsCompact {x : v.adicCompletion ℚ | ‖x‖ ≤ X} := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt X (one_lt_absNorm_real v)
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp (n : ℤ))
  have hy₀0 : y₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hy₀
    exact WithZero.exp_ne_zero hy₀.symm
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  have hsub : {x : v.adicCompletion ℚ | ‖x‖ ≤ X} ⊆
      (fun x => y₀ * x) '' (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    intro x hx
    have hxn : ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (n : ℤ) := by
      rw [zpow_natCast]
      exact (le_of_lt (lt_of_le_of_lt hx hn))
    have hvx : Valued.v x ≤ WithZero.exp (n : ℤ) := valued_le_of_norm_le_zpow v hxn
    refine ⟨y₀⁻¹ * x, ?_, show y₀ * (y₀⁻¹ * x) = x by rw [← mul_assoc, mul_inv_cancel₀ hy₀0, one_mul]⟩
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hy₀]
    calc (WithZero.exp (n : ℤ))⁻¹ * Valued.v x ≤ (WithZero.exp (n : ℤ))⁻¹ * WithZero.exp (n : ℤ) :=
          mul_le_mul_right hvx _
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
  exact (hO.image (continuous_const.mul continuous_id)).of_isClosed_subset
    (isClosed_le continuous_norm continuous_const) hsub

private theorem exists_finset_forall_jacquetValue_dualTranslate_eq_sum (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (δ : ℝ) (S : Finset (v.adicCompletion ℚ)), 0 < δ ∧ δ ≤ 1 ∧
      (∀ y₁ ∈ S, ∀ y₂ ∈ S, y₁ ≠ y₂ → Disjoint (Metric.ball y₁ δ) (Metric.ball y₂ δ)) ∧
      ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
        jacquetValue v (dualTranslate v ν Φ a x) =
          ∑ y ∈ S, jacquetValue v (dualTranslate v ν Φ a y) *
            (Metric.ball y δ).indicator (fun _ => (1 : ℂ)) x := by
  classical
  obtain ⟨X₀, hX₀⟩ := exists_forall_lt_norm_jacquetValue_dualTranslate_eq_zero v ν Φ hν hΦl hΦc
  obtain ⟨δ₀, hδ₀0, hδ₀⟩ := exists_forall_jacquetValue_dualTranslate_add_eq v ν Φ hν hΦl hΦc
  set δ : ℝ := min δ₀ 1 with hδ_def
  have hδ0 : 0 < δ := lt_min hδ₀0 zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  obtain ⟨T, -, hTfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_setOf_norm_le v (max X₀ 0)) hδ0
  set Bs : Finset (Set (v.adicCompletion ℚ)) := hTfin.toFinset.image fun z => Metric.ball z δ with hBs_def
  have hrep : ∀ B ∈ Bs, ∃ z : v.adicCompletion ℚ, Metric.ball z δ = B := by
    intro B hB
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨z, rfl⟩
  choose! rep hrep' using hrep
  refine ⟨δ, Bs.image rep, hδ0, hδ1, ?_, fun a x => ?_⟩
  · intro y₁ hy₁ y₂ hy₂ hne
    obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.mp hy₁
    obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_image.mp hy₂
    rcases IsUltrametricDist.ball_eq_or_disjoint (x := rep B₁) (y := rep B₂) (r := δ) with h | h
    · exfalso
      apply hne
      have hBB : B₁ = B₂ := by rw [← hrep' B₁ hB₁, ← hrep' B₂ hB₂, h]
      rw [hBB]
    · exact h
  · by_cases hx : ∃ y ∈ Bs.image rep, x ∈ Metric.ball y δ
    · obtain ⟨y₀, hy₀S, hxy₀⟩ := hx
      rw [Finset.sum_eq_single y₀ ?_ (fun h => absurd hy₀S h)]
      · rw [Set.indicator_of_mem hxy₀, mul_one, show x = y₀ + (x - y₀) by ring]
        apply hδ₀
        rw [Metric.mem_ball, dist_eq_norm] at hxy₀
        exact hxy₀.le.trans hδδ₀
      · intro y hyS hne
        have hdis : Disjoint (Metric.ball y δ) (Metric.ball y₀ δ) := by
          obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.mp hyS
          obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_image.mp hy₀S
          rcases IsUltrametricDist.ball_eq_or_disjoint (x := rep B₁) (y := rep B₂) (r := δ) with h | h
          · exfalso
            apply hne
            have hBB : B₁ = B₂ := by rw [← hrep' B₁ hB₁, ← hrep' B₂ hB₂, h]
            rw [hBB]
          · exact h
        rw [Set.indicator_of_notMem (fun hxy => Set.disjoint_left.mp hdis hxy hxy₀), mul_zero]
    · have hx' : ∀ y ∈ Bs.image rep, x ∉ Metric.ball y δ := fun y hy hxy => hx ⟨y, hy, hxy⟩
      rw [Finset.sum_eq_zero fun y hy => by rw [Set.indicator_of_notMem (hx' y hy), mul_zero]]
      apply hX₀ a x
      rcases lt_or_ge X₀ ‖x‖ with hlt | hle
      · exact hlt
      · exfalso
        have hxC : x ∈ {x : v.adicCompletion ℚ | ‖x‖ ≤ max X₀ 0} := hle.trans (le_max_left _ _)
        obtain ⟨z, hzT, hxz⟩ := Set.mem_iUnion₂.mp (hcover hxC)
        have hB : Metric.ball z δ ∈ Bs := Finset.mem_image.mpr ⟨z, hTfin.mem_toFinset.mpr hzT, rfl⟩
        refine hx' (rep (Metric.ball z δ)) (Finset.mem_image_of_mem rep hB) ?_
        rw [hrep' _ hB]
        exact hxz

private theorem selfDualHaarAt_ball (y : v.adicCompletion ℚ) (δ : ℝ) :
    selfDualHaarAt ℚ v (Metric.ball y δ) = selfDualHaarAt ℚ v (Metric.ball 0 δ) := by
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hset : Metric.ball y δ = (fun t => -y + t) ⁻¹' Metric.ball 0 δ := by
    ext t
    simp only [Metric.mem_ball, Set.mem_preimage, dist_eq_norm, sub_zero, neg_add_eq_sub]
  rw [hset, measure_preimage_add]

private theorem selfDualHaarAt_ball_lt_top (y : v.adicCompletion ℚ) {δ : ℝ} (hδ : δ ≤ 1) :
    selfDualHaarAt ℚ v (Metric.ball y δ) < ⊤ := by
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  rw [selfDualHaarAt_ball v y δ]
  refine lt_of_le_of_lt (measure_mono fun t ht => ?_) hO.measure_lt_top
  rw [Metric.mem_ball, dist_zero_right] at ht
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : ‖t‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (0 : ℤ) := by
    rw [zpow_zero]
    exact (ht.trans_le hδ).le
  simpa using valued_le_of_norm_le_zpow v h1

private theorem integrable_indicator_ball (y : v.adicCompletion ℚ) {δ : ℝ} (hδ : δ ≤ 1) :
    Integrable ((Metric.ball y δ).indicator fun _ => (1 : ℂ)) (selfDualHaarAt ℚ v) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  exact (integrableOn_const (hs := (selfDualHaarAt_ball_lt_top v y hδ).ne)).integrable_indicator
    measurableSet_ball

private theorem exists_finset_forall_dualFn_eq_mul_sum_dualSlice' (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (S : Finset (v.adicCompletion ℚ)) (c : ℂ), ∀ t : v.adicCompletion ℚ,
      dualFn v ν Φ t = c * ∑ x ∈ S, dualSlice v ν Φ x t := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  obtain ⟨δ, S, hδ0, hδ1, -, hnet⟩ := exists_finset_forall_jacquetValue_dualTranslate_eq_sum v ν Φ hν hΦl hΦc
  refine ⟨S, (((selfDualHaarAt ℚ v).real (Metric.ball 0 δ) : ℝ) : ℂ), fun t => ?_⟩
  by_cases ht : t = 0
  · simp [ht, dualFn_zero, dualSlice_zero]
  · have hint : ∀ y ∈ S, Integrable (fun x => jacquetValue v (dualTranslate v ν Φ (Units.mk0 t ht) y) *
        (Metric.ball y δ).indicator (fun _ => (1 : ℂ)) x) (selfDualHaarAt ℚ v) :=
      fun y _ => (integrable_indicator_ball v y hδ1).const_mul _
    simp only [dualFn, dualSlice, dif_neg ht]
    rw [show (fun x => jacquetValue v (dualTranslate v ν Φ (Units.mk0 t ht) x)) =
        fun x => ∑ y ∈ S, jacquetValue v (dualTranslate v ν Φ (Units.mk0 t ht) y) *
          (Metric.ball y δ).indicator (fun _ => (1 : ℂ)) x from funext fun x => hnet _ x,
      integral_finsetSum S hint, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_const_mul, integral_indicator_const (1 : ℂ) measurableSet_ball,
      show (selfDualHaarAt ℚ v).real (Metric.ball y δ) = (selfDualHaarAt ℚ v).real (Metric.ball 0 δ) by
        rw [measureReal_def, measureReal_def, selfDualHaarAt_ball v y δ],
      Complex.real_smul, mul_one]
    ring

end DualNet
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"

end WeylTranslateZeta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum.WeylTranslateZeta"

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open WeylTranslateZeta

open LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    letI := localBorel ℚ v
    (∀ x : v.adicCompletion ℚ, ∀ F : v.adicCompletion ℚ → ℂ, F 0 = 0 →
      (∀ a : (v.adicCompletion ℚ)ˣ,
        F a = jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
            (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
              antidiagonal3 v)
            (cellSectionOf v ν Φ)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
      ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, F t' = F t) ∧
    (∀ G : v.adicCompletion ℚ → ℂ, G 0 = 0 →
      (∀ a : (v.adicCompletion ℚ)ˣ,
        G a = (∫ x : v.adicCompletion ℚ, jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
              (longWeyl3 *
                  transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
                antidiagonal3 v)
            (cellSectionOf v ν Φ)) ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
      ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, G t' = G t) ∧
    (∃ B : ℝ,
      (∀ x : v.adicCompletion ℚ, ∀ F : v.adicCompletion ℚ → ℂ, F 0 = 0 →
        (∀ a : (v.adicCompletion ℚ)ˣ,
          F a = jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
              (longWeyl3 *
                  transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
                antidiagonal3 v)
              (cellSectionOf v ν Φ)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
        ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → F t = 0) ∧
      (∀ G : v.adicCompletion ℚ → ℂ, G 0 = 0 →
        (∀ a : (v.adicCompletion ℚ)ˣ,
          G a = (∫ x : v.adicCompletion ℚ, jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
                (longWeyl3 *
                    transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
                  antidiagonal3 v)
              (cellSectionOf v ν Φ)) ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
        ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → G t = 0)) ∧
    ∃ (S : Finset (v.adicCompletion ℚ)) (c : ℂ), ∀ a : (v.adicCompletion ℚ)ˣ,
      (∫ x : v.adicCompletion ℚ, jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
            (longWeyl3 *
                transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
              antidiagonal3 v)
          (cellSectionOf v ν Φ)) ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ =
        c * (∑ x ∈ S,
          jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
              (longWeyl3 *
                  transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
                antidiagonal3 v)
              (cellSectionOf v ν Φ)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) := by
  refine ⟨fun x F hF0 hFa t ht => ?_, fun G hG0 hGa t ht => ?_, ?_, ?_⟩
  · obtain rfl : F = dualSlice v ν Φ x := by
      funext s
      by_cases hs : s = 0
      · rw [hs, hF0, dualSlice_zero]
      · have h := hFa (Units.mk0 s hs)
        simp only [Units.val_mk0] at h
        rw [h, dualSlice, dif_neg hs]
        rfl
    exact eventually_dualSlice_eq v ν Φ hν hΦl hΦc x ht
  · obtain rfl : G = dualFn v ν Φ := by
      funext s
      by_cases hs : s = 0
      · rw [hs, hG0, dualFn_zero]
      · have h := hGa (Units.mk0 s hs)
        have h' := dualFn_coe_units v ν Φ (Units.mk0 s hs)
        simp only [Units.val_mk0] at h h'
        rw [h, h']
        rfl
    exact eventually_dualFn_eq' v ν Φ hν hΦl hΦc t ht
  · obtain ⟨B, hB⟩ := exists_forall_dualSlice_eq_zero_of_lt v ν Φ hν hΦl hΦc
    obtain ⟨S, c, hnet⟩ := exists_finset_forall_dualFn_eq_mul_sum_dualSlice' v ν Φ hν hΦl hΦc
    refine ⟨B, fun x F hF0 hFa t ht => ?_, fun G hG0 hGa t ht => ?_⟩
    · obtain rfl : F = dualSlice v ν Φ x := by
        funext s
        by_cases hs : s = 0
        · rw [hs, hF0, dualSlice_zero]
        · have h := hFa (Units.mk0 s hs)
          simp only [Units.val_mk0] at h
          rw [h, dualSlice, dif_neg hs]
          rfl
      exact hB x t ht
    · obtain rfl : G = dualFn v ν Φ := by
        funext s
        by_cases hs : s = 0
        · rw [hs, hG0, dualFn_zero]
        · have h := hGa (Units.mk0 s hs)
          have h' := dualFn_coe_units v ν Φ (Units.mk0 s hs)
          simp only [Units.val_mk0] at h h'
          rw [h, h']
          rfl
      rw [hnet t, Finset.sum_eq_zero fun x _ => hB x t ht, mul_zero]
  · obtain ⟨S, c, hnet⟩ := exists_finset_forall_dualFn_eq_mul_sum_dualSlice' v ν Φ hν hΦl hΦc
    refine ⟨S, c, fun a => ?_⟩
    have h := hnet a
    rw [dualFn_coe_units] at h
    simp only [dualSlice, dif_neg a.ne_zero, Units.mk0_val] at h
    exact h

end S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_dualJacquetValueSlices_eventually_eq_and_eq_zero_and_eq_mul_sum (solution)
